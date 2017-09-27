//--*- C++ -*-
//===-- MakeStackTraceable.cpp - Mirror JS variables on linear stack -------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===-----------------------------------------------------------------------===//
//
// Ensure that the value of every live LLVM IR virtual register that may hold an address
// of a heap object has a copy on on the linear memory stack at each function call.  This
// guarantees that all live heap objects can be traced during a scan of the linear memory stack.
//
//===-----------------------------------------------------------------------===//

//#include "OptPasses.h"

#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Constants.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/ADT/SetOperations.h"
//#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Debug.h"
//#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
//#include "llvm/Transforms/Utils/BasicBlockUtils.h"	// FoldingSingleEntryPHINodes
//#include "llvm/Transforms/Utils/Local.h"		// removeUnreachableBlocks

#define DEBUG_TYPE "make-stack-traceable"

// Uncomment this to force additional consistency checking in a release build.
//#undef NDEBUG

// When defined, add 'llvm.lifetime.start' and 'llvm.lifetime.end' intrinsics for the
// mirror stack slots, limiting their lifetime to that of the underlying LLVM virtual register.
// This should allow Emscripten to reduce the number of slots that must actually be allocated.
// Not only does this reduce the size of the frame on the linear memory stack, but it reduces
// the number of variables in the generated asm.js code.
#define ANNOTATE_MIRROR_LIFETIMES

// Diagnostics
//#define TRACE_MIRROR_LIFETIMES


using namespace llvm;

//================================================================================    

struct MakeStackTraceable : public FunctionPass {
  static char ID;
  MakeStackTraceable() : FunctionPass(ID) {
    //    initializeMakeStackTraceablePass(*PassRegistry::getPassRegistry());
  }

  bool runOnFunction(Function &F) override;

  const char *getPassName() const override { return "MakeStackTraceable"; }
};
  
char MakeStackTraceable::ID = 0;
//INITIALIZE_PASS(MakeStackTraceable, "make-stack-traceable", "Force values to linear memory stack", false, false)

namespace llvm {

  FunctionPass *createEmscriptenMakeStackTraceablePass() {
  return new MakeStackTraceable();
}
  
} // namespace llvm


typedef SetVector<Value *> LiveSetTy;  
  
struct GCPtrLivenessData {

  // Values defined in this block.
  MapVector<BasicBlock *, LiveSetTy> KillSet;
  
  // Values used in this block (and thus live); does not included values
  // killed within this block.
  MapVector<BasicBlock *, LiveSetTy> LiveSet;

  // Values live into this basic block (i.e. used by any
  // instruction in this basic block or ones reachable from here)
  MapVector<BasicBlock *, LiveSetTy> LiveIn;

  // Values live out of this basic block (i.e. live into
  // any successor block)
  MapVector<BasicBlock *, LiveSetTy> LiveOut;
};

// Compute the live-in and live-out sets for every basic block in the function.

static void computeGCPtrLivenessData(DominatorTree &DT, Function &F, GCPtrLivenessData &Data);

// Given results from the dataflow liveness computation, find the set of live Values at a particular instruction.

static void findLiveSetAtInst(Instruction *inst, GCPtrLivenessData &Data, LiveSetTy &out);

// We cannot currently distinguish pointers via type, due to type-punning
// in the definition of Atom, etc., thus we include all pointer-sized scalars.
// We assume all non-scalar objects are on the linear stack (or in the heap) only.

static bool isGCPointerType(Type *T) {
  return T->isIntegerTy(32) || T->isPointerTy();
}

// Determine (conservatively) whether an address refers to a location on the stack.
// We want to avoid creating mirrors for these, because they are already visible to
// a stack scan.

static bool isAllocaBased(Value *V) {
  while (isa<BitCastInst>(V) || isa<GetElementPtrInst>(V))
  {
    Instruction* Inst = dyn_cast<Instruction>(V);
    assert(Inst);
    V = Inst->getOperand(0);
  }
  return isa<AllocaInst>(V);
}

static bool needsStatePoint(Instruction &I) {
  // Conservatively assume that any non-intrinsic call may invoke GC, directly or indirectly.
  if (ImmutableCallSite CS = ImmutableCallSite(&I)) {
    if (auto *F = CS.getCalledFunction()) {
      return !(F->isIntrinsic() || F->getIntrinsicID() != Intrinsic::not_intrinsic || F->getName().startswith("@"));
    } else {
      return true;  // indirect call
    }
  }
  return false;
}

struct StatePoint {
  
  // The set of values that needs to be saved at this call site.
  LiveSetTy SaveSet;
  
  // The call site that needs to be protected.
  Instruction* CallInstruction;

};

static void walkDomTreeNodes(DomTreeNode* N,				// Current node in dominator tree
			     Function &F,				// Current function (constant for entire walk)
			     GCPtrLivenessData &LivenessData,		// GC ptr liveness information for entire function
			     SetVector<Value *> Saved,			// Values mirrored in dominating blocks (pass by copy)
			     MapVector<Value *, Value *> &Mirrors,	// Value -> Mirror map for values mirrored thus far
			     SmallVector<StatePoint, 64> &StatePoints)	// Collected calls sites and live Value information
{
  BasicBlock* BB = N->getBlock();
  
  if (BB) {

    // FIXME: Make a single backwards pass over the block instead of repeatedly calling findLiveSetAtInst().

    for (Instruction &I : *BB) {
      if (needsStatePoint(I)) {
	Instruction *Inst = &I;

	// Find Values live at this instruction.
	LiveSetTy LiveSet;
	findLiveSetAtInst(Inst, LivenessData, LiveSet);

	// Record instruction and the set of Values to save in the StatePoints vector for later processing.
	// We save all live Values that have not already been saved, either in a dominator or previously
	// within the current block.
	LiveSet.set_subtract(Saved);
	StatePoints.push_back({LiveSet, Inst});	

#ifdef TRACE_MIRROR_LIFETIMES
	for (Value *V : LiveSet) {	
	  dbgs() << "MIRROR OF ";
	  V->printAsOperand(dbgs(), false, F.getParent());
	  dbgs() << " LIVE AT " << *Inst << "\n";
	}
#endif
	
	// Saved values need not be saved again, whether saved in this block, or in a dominator.
	Saved.set_union(LiveSet);
      }
    }

    // Continue traversal of the dominator tree, collecting statepoints.
    const std::vector<DomTreeNode *> &Children = N->getChildren();
    for (DomTreeNode* Child : Children) {
      walkDomTreeNodes(Child, F, LivenessData, Saved, Mirrors, StatePoints);
    }
    
  } else {
    // Unreachable blocks may result in empty dominator tree nodes.
    // We expect earlier optimization passes to have removed these, so we abort if we see one.
    dbgs() << "Unreachable block:\n" << *BB << "\n";
    abort();
  }
}
  
static const int int32bytes = 4;

static bool walkDominatorTree(DominatorTree &DT, Function &F)
{
  SetVector<Value *> Saved;
  MapVector<Value *, Value *> Mirrors;
  SmallVector<StatePoint, 64> StatePoints;
  GCPtrLivenessData LivenessData;

  // Collect GC pointer liveness data for the entire function.
  computeGCPtrLivenessData(DT, F, LivenessData);

  // Walk the dominator tree, collecting relevant call sites and the values that
  // must be saved to the linear memory stack at each such call site.
  walkDomTreeNodes(DT.getRootNode(), F, LivenessData, Saved, Mirrors, StatePoints);

  // Do rewrites

  bool MadeChange = false;  

  for (StatePoint PP : StatePoints) {

    LiveSetTy& SaveSet = PP.SaveSet;
    Instruction* Inst  = PP.CallInstruction;

    for (Value *V : SaveSet) {
      if (auto *I = dyn_cast<Instruction>(V)) {

	// Create a mirror for the value if one does not already exist.
	Value *Mirror = Mirrors[V];
	if (!Mirror) {
	  assert(V->getType() && isGCPointerType(V->getType()));
	  // Insert a new AllocaInst at the start of the entry block, following any phi nodes.
	  IRBuilder<> IRB(&*F.getEntryBlock().getFirstInsertionPt());
	  Mirror = IRB.CreateAlloca(V->getType(), nullptr, "mirror");
	  Mirrors[V] = Mirror;
	}	

	// Save a copy of the value into the mirror.
	IRBuilder<> IRB(Inst);
	IRB.CreateStore(I, Mirror);
	
#ifdef ANNOTATE_MIRROR_LIFETIMES
	// Annotate the mirror with the start of its lifetime.
	Module *M = F.getParent();
	LLVMContext &Ctx = M->getContext();	
	auto LifetimeStart = Intrinsic::getDeclaration(M, Intrinsic::lifetime_start);
	auto *I8Ptr = Type::getInt8Ty(Ctx)->getPointerTo();
	auto *BufPtr = IRB.CreateBitCast(Mirror, I8Ptr, "mirror_lifetime_bitcast");
	auto *BufSize = ConstantInt::get(Ctx, APInt(32, int32bytes));
	IRB.CreateCall(LifetimeStart, {BufSize, BufPtr});
#endif
	MadeChange = true;
      } else {
	assert(!"bad instruction in live set");
      }
    }
  }

#ifdef ANNOTATE_MIRROR_LIFETIMES  
  
  for (BasicBlock &BB : F) {

    LiveSetTy LiveOut = LivenessData.LiveOut[&BB];  // make copy here!

    struct LastUseInfo {
      Value* LastUser;
      Value* Mirror;
    };

    SmallVector<LastUseInfo, 64> LastUses;
    
    // Iterate over instructions of each basic block in reverse.
    for (auto &I : make_range(BB.rbegin(), BB.rend())) {
      for(Use &U : I.operands()){
	Value *V = U.get();

	if (!LiveOut.count(V)) {
	  // Not live out, or occuring later in this block, so dead here.
	  Value *Mirror = Mirrors[V];
	  if (Mirror) {
#ifdef TRACE_MIRROR_LIFETIMES
	    dbgs() << "MIRROR OF ";
	    V->printAsOperand(dbgs(), false, F.getParent());
	    dbgs() << " DEAD AT " << I << "\n";
#endif
	    LastUses.push_back({&I, Mirror});
	  }
	  // Add to LiveOut (though not actually so) to avoid taking this path again.
	  LiveOut.insert(V);
	}
      }
    }

    for (auto &LUI : LastUses) {
      Instruction* Inst = dyn_cast<Instruction>(LUI.LastUser);
      assert(Inst);
      Instruction* Mirror = dyn_cast<Instruction>(LUI.Mirror);
      assert(Mirror);
      Module *M = F.getParent();
      LLVMContext &Ctx = M->getContext();
      auto LifetimeEnd = Intrinsic::getDeclaration(M, Intrinsic::lifetime_end);
      auto *I8Ptr = Type::getInt8Ty(Ctx)->getPointerTo();

      if (Inst->isTerminator()) {
	// We cannot insert after the terminator in the current block, so we must
	// insert instead at entry to each of the successor blocks.
	for (BasicBlock *Succ : successors(Inst->getParent())) {
	  Instruction* InsertPt = &*Succ->getFirstInsertionPt();  // skip phi nodes
	  IRBuilder<> IRB(InsertPt);
	  auto *BufPtr = IRB.CreateBitCast(Mirror, I8Ptr, "mirror_lifetime_bitcast");
	  auto *BufSize = ConstantInt::get(Ctx, APInt(32, int32bytes));
	  IRB.CreateCall(LifetimeEnd, {BufSize, BufPtr});	    
	}
      } else {
	// We want to insert after Inst, which means *before* the following instruction.
	// Since Inst is not a terminator, we know that such an instruction must exist.
	Instruction* InsertPt = dyn_cast<Instruction>(Inst->getNextNode());
	assert(InsertPt);
	
	// The last use may be a phi node, but we cannot insert anything in the
	// middle of a sequence of phi nodes, as it is assumed in many places that
	// all phi nodes in a block occur contiguously at the beginning.  Skip over
	// any phi nodes and insert before the following instruction.  Note that such
	// an instruction must exist, as the block must end with a branch.

	while (isa<PHINode>(InsertPt)) {
	  InsertPt = dyn_cast<Instruction>(InsertPt->getNextNode());
	}
	assert(InsertPt);

	IRBuilder<> IRB(InsertPt);
	auto *BufPtr = IRB.CreateBitCast(Mirror, I8Ptr, "mirror_lifetime_bitcast");
	auto *BufSize = ConstantInt::get(Ctx, APInt(32, int32bytes));
	IRB.CreateCall(LifetimeEnd, {BufSize, BufPtr});
      }

      MadeChange = true;
    }
  }
  #endif
  
  return MadeChange;
}

bool MakeStackTraceable::runOnFunction(Function &F) {

#ifdef TRACE_MIRROR_LIFETIMES
  dbgs() << "MakeStackTraceable: ";
  dbgs().write_escaped(F.getName()) << '\n';
#endif

  // Nothing to do for declarations.
  if (F.isDeclaration() || F.empty())
    return false;

  bool MadeChange = false;

#if 0
  // As a prepass, go ahead and aggressively destroy single entry phi nodes.
  // These are created by LCSSA.  They have the effect of increasing the size
  // of liveness sets for no good reason.
  for (BasicBlock &BB : F) {
    if (BB.getUniquePredecessor()) {
      MadeChange = true;
      FoldSingleEntryPHINodes(&BB);
    }
  }
#endif

  DominatorTreeWrapperPass DTW;
  DTW.runOnFunction(F);
  DominatorTree &DT = DTW.getDomTree();

  //  if (HasUnreachableStatepoint)
  //    MadeChange |= removeUnreachableBlocks(F);

  MadeChange |= walkDominatorTree(DT, F);

#if 0
  dbgs() << "Final IR after MakeStackTraceable pass:\n";
  for (BasicBlock &BB : F)
    dbgs() << BB << "\n";
#endif  

  return MadeChange;
}

//================================================================================
//
// Liveness computation via standard iterative dataflow analysis.
//
// Code stolen shamelessly from lib/Transforms/Scalar/RewriteStatepointsForGC.cpp.
//
// Modified criteria for filtering values interesting to GC: We want pointers and
// integers of pointer size (which may be addresses), except those that are known
// to be addresses of objects within the linear stack.
//
//================================================================================

/// Compute the live-in set for the location rbegin starting from
/// the live-out set of the basic block
static void computeLiveInValues(BasicBlock::reverse_iterator Begin,
                                BasicBlock::reverse_iterator End,
                                SetVector<Value *> &LiveTmp) {
  for (auto &I : make_range(Begin, End)) {
    // KILL/Def - Remove this definition from LiveIn
    LiveTmp.remove(&I);

    // Don't consider *uses* in PHI nodes, we handle their contribution to
    // predecessor blocks when we seed the LiveOut sets.
    if (isa<PHINode>(I))
      continue;

    // USE - Add to the LiveIn set for this instruction
    for (Value *V : I.operands()) {
      if (isGCPointerType(V->getType()) && !isa<Constant>(V) && !isAllocaBased(V)) {
        // The choice to exclude all things constant here is slightly subtle.
        // There are two independent reasons:
        // - We assume that things which are constant (from LLVM's definition)
        // do not move at runtime.  For example, the address of a global
        // variable is fixed, even though it's contents may not be.
        // - Second, we can't disallow arbitrary inttoptr constants even
        // if the language frontend does.  Optimization passes are free to
        // locally exploit facts without respect to global reachability.  This
        // can create sections of code which are dynamically unreachable and
        // contain just about anything.  (see constants.ll in tests)
        LiveTmp.insert(V);
      }
    }
  }
}

static void computeLiveOutSeed(BasicBlock *BB, SetVector<Value *> &LiveTmp) {
  for (BasicBlock *Succ : successors(BB)) {
    for (auto &I : *Succ) {
      PHINode *PN = dyn_cast<PHINode>(&I);
      if (!PN)
        break;

      Value *V = PN->getIncomingValueForBlock(BB);
      if (isGCPointerType(V->getType()) && !isa<Constant>(V) && !isAllocaBased(V)) {
        LiveTmp.insert(V);
      }
    }
  }
}

static SetVector<Value *> computeKillSet(BasicBlock *BB) {
  SetVector<Value *> KillSet;
  for (Instruction &I : *BB)
    if (isGCPointerType(I.getType()))
      KillSet.insert(&I);
  return KillSet;
}

#ifndef NDEBUG
/// Check that the items in 'Live' dominate 'TI'.  This is used as a basic
/// sanity check for the liveness computation.
static void checkBasicSSA(DominatorTree &DT, SetVector<Value *> &Live,
                          TerminatorInst *TI, bool TermOkay = false) {
  for (Value *V : Live) {
    if (auto *I = dyn_cast<Instruction>(V)) {
      // The terminator can be a member of the LiveOut set.  LLVM's definition
      // of instruction dominance states that V does not dominate itself.  As
      // such, we need to special case this to allow it.
      if (TermOkay && TI == I)
        continue;
      assert(DT.dominates(I, TI) &&
             "basic SSA liveness expectation violated by liveness analysis");
    }
  }
}

/// Check that all the liveness sets used during the computation of liveness
/// obey basic SSA properties.  This is useful for finding cases where we miss
/// a def.
static void checkBasicSSA(DominatorTree &DT, GCPtrLivenessData &Data,
                          BasicBlock &BB) {
  checkBasicSSA(DT, Data.LiveSet[&BB], BB.getTerminator());
  checkBasicSSA(DT, Data.LiveOut[&BB], BB.getTerminator(), true);
  checkBasicSSA(DT, Data.LiveIn[&BB], BB.getTerminator());
}
#endif

static void computeGCPtrLivenessData(DominatorTree &DT, Function &F, GCPtrLivenessData &Data)
{
  SmallSetVector<BasicBlock *, 32> Worklist;

  // Seed the liveness for each individual block
  for (BasicBlock &BB : F) {
    // These are the values defined in block BB.
    Data.KillSet[&BB] = computeKillSet(&BB);
    Data.LiveSet[&BB].clear();
    // These are the values used in block BB.
    computeLiveInValues(BB.rbegin(), BB.rend(), Data.LiveSet[&BB]);

#ifndef NDEBUG
    for (Value *Kill : Data.KillSet[&BB])
      assert(!Data.LiveSet[&BB].count(Kill) && "live set contains kill");
#endif

    Data.LiveOut[&BB] = SetVector<Value *>();
    // These are the values used by Phi-nodes in immediate successors.
    computeLiveOutSeed(&BB, Data.LiveOut[&BB]);
    // LiveIn = (LiveOut U LiveSet) - KillSet
    // This differs from the common textbook formulation in terms of GEN and KILL.
    // LiveSet includes all uses, including those that are defined within the block,
    // and might better be called UsedSet.  Note that a use cannot occur before its
    // definition in a block, therefore GEN = LiveSet - KILL, and this formulation is
    // equivalent to LiveIn = GEN U (LiveOut - KILL).
    Data.LiveIn[&BB] = Data.LiveSet[&BB];
    Data.LiveIn[&BB].set_union(Data.LiveOut[&BB]);
    Data.LiveIn[&BB].set_subtract(Data.KillSet[&BB]);
    if (!Data.LiveIn[&BB].empty())
      Worklist.insert(pred_begin(&BB), pred_end(&BB));
  }

  // Propagate that liveness until stable
  while (!Worklist.empty()) {
    BasicBlock *BB = Worklist.pop_back_val();

    // Compute our new liveout set, then exit early if it hasn't changed despite
    // the contribution of our successor.
    SetVector<Value *> LiveOut = Data.LiveOut[BB];
    const auto OldLiveOutSize = LiveOut.size();

      for (BasicBlock *Succ : successors(BB)) {
      assert(Data.LiveIn.count(Succ));
      LiveOut.set_union(Data.LiveIn[Succ]);
    }
    // assert OutLiveOut is a subset of LiveOut
    if (OldLiveOutSize == LiveOut.size()) {
      // If the sets are the same size, then we didn't actually add anything
      // when unioning our successors LiveIn.  Thus, the LiveIn of this block
      // hasn't changed.
      continue;
    }
    Data.LiveOut[BB] = LiveOut;

    // Apply the effects of this basic block
    SetVector<Value *> LiveTmp = LiveOut;
    LiveTmp.set_union(Data.LiveSet[BB]);
    LiveTmp.set_subtract(Data.KillSet[BB]);

    assert(Data.LiveIn.count(BB));
    const SetVector<Value *> &OldLiveIn = Data.LiveIn[BB];
    // assert: OldLiveIn is a subset of LiveTmp
    if (OldLiveIn.size() != LiveTmp.size()) {
      Data.LiveIn[BB] = LiveTmp;
      Worklist.insert(pred_begin(BB), pred_end(BB));
    }
  } // while (!Worklist.empty())

#ifndef NDEBUG
  // Sanity check our output against SSA properties.  This helps catch any
  // missing kills during the above iteration.
  for (BasicBlock &BB : F)
    checkBasicSSA(DT, Data, BB);
#endif

#if 0
  // Dump blocks and computed liveness data for diagnostic purposes.
  for (BasicBlock &BB : F) {
    dbgs() << "Block:\n";
    dbgs() << BB << "\n";
    dbgs() << "LiveIn:\n";
    for (Value *V : Data.LiveIn[&BB])
      dbgs() << *V << "\n";
    dbgs() << "KillSet:\n";    
    for (Value *V : Data.KillSet[&BB])
      dbgs() << *V << "\n";
    dbgs() << "LiveOut:\n";
    for (Value *V : Data.LiveOut[&BB])
      dbgs() << *V << "\n";    
    dbgs() << "\n";
  }
#endif
}

static void findLiveSetAtInst(Instruction *Inst, GCPtrLivenessData &Data,
                              LiveSetTy &Out) {

  BasicBlock *BB = Inst->getParent();

  // Note: The copy is intentional and required.
  assert(Data.LiveOut.count(BB));
  SetVector<Value *> LiveOut = Data.LiveOut[BB];
  BasicBlock::reverse_iterator rend(Inst->getIterator());
  computeLiveInValues(BB->rbegin(), rend, LiveOut);
  LiveOut.remove(Inst);
  Out.insert(LiveOut.begin(), LiveOut.end());
}
