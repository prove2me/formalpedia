-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CyclicRaw.compileRaw_erase
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:50:52.423261+00:00
-- url     : https://prove2.me/submissions/ae77b196-3978-4cf0-96db-09a995c82a4e

/- Generated from Solutions.CyclicRawCorrectness by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockClockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockImplements
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockProgramPlacement
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockStateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockTaggedActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCompilerCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingActions
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateEtaTransport
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHadamardCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateInitialization
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterHistory
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateOldPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificatePostCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificatePreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateQuantumTransports
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateRangeCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateStageActions
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidity
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentAcceptance
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicVerifier
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawArithmeticGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCertificateGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RawControlGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawThresholdGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding
import Theorems.Thm_QMAPerfectCompleteness_Main_CyclicRaw_historyLayout_raw
import Theorems.Thm_QMAPerfectCompleteness_Main_CyclicRaw_rangeLayout_raw

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
end QMAPerfectCompleteness.Main.BlockHistoryCoordinates
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Main.CoordinateFibers
end QMAPerfectCompleteness.Main.CoordinateFibers
namespace QMAPerfectCompleteness.Main.CertificateClaimBits
end QMAPerfectCompleteness.Main.CertificateClaimBits
namespace QMAPerfectCompleteness.Main.CertificateReadoutEffect
end QMAPerfectCompleteness.Main.CertificateReadoutEffect
namespace QMAPerfectCompleteness.Main.CertificateVerifierEffect
end QMAPerfectCompleteness.Main.CertificateVerifierEffect

/- Inline helpers retained from Solutions.ControlCircuits. -/
section


/-! Concrete prefix-AND and many-control circuits for the block compiler. -/

open Matrix
namespace QMAPerfectCompleteness.Main.ControlCircuits
open ReversibleGadgets



variable {r n : ℕ} (L : AndLayout r n)























































/-- The recursive prefix list agrees with the canonical increasing finRange order. -/
theorem prefixGates_eq_map (t : ℕ) (ht : t ≤ r) :
    prefixGates L t ht = (List.finRange t).map
      (fun j : Fin t => andStep L ⟨j, Nat.lt_of_lt_of_le j.isLt ht⟩) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [prefixGates, List.finRange_succ_last, List.map_append, List.map_map,
      List.map_singleton]
    rw [ih (by omega)]
    rfl

theorem prefixGates_full_eq_map :
    prefixGates L r le_rfl = (List.finRange r).map (andStep L) := by
  rw [prefixGates_eq_map]

theorem andGates_eq_map :
    andGates L = [xAt (L.flags 0)] ++ (List.finRange r).map (andStep L) := by
  rw [andGates, prefixGates_full_eq_map]



end QMAPerfectCompleteness.Main.ControlCircuits


end

/- Inline helpers retained from Solutions.RawG2Gadgets. -/
section


/-! Executable G₂ instruction templates. Matrices and circuit-proof data never occur here. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.RawG2
open RawEncoding ReversibleGadgets ControlCircuits EqualityCircuits








@[simp] theorem erase_x {n : ℕ} (w : Fin n) : eraseInstr (xAt w)=x w.val := rfl
@[simp] theorem erase_cn {n : ℕ} (e : Fin 2 ↪ Fin n) : eraseInstr (cnotAt e)=cn (e 0).val (e 1).val := rfl
@[simp] theorem erase_tof {n : ℕ} (e : Fin 3 ↪ Fin n) : eraseInstr (toffoliAt e)=tof (e 0).val (e 1).val (e 2).val := rfl


lemma erase_mapWires {G : GateSet} {r n : ℕ} (e : Fin r ↪ Fin n) (f : ℕ → ℕ)
    (he : ∀j,(e j).val=f j.val) (i : Instr G r) :
    eraseInstr (i.mapWires e)=⟨(eraseInstr i).gate,(eraseInstr i).wires.map f⟩ := by
  simp only [eraseInstr,Instr.mapWires,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  exact he (i.targets j)

lemma erase_mapGates {G : GateSet} {r n : ℕ} (e : Fin r ↪ Fin n) (f : ℕ → ℕ)
    (he : ∀j,(e j).val=f j.val) (gs : List (Instr G r)) :
    (gs.map (Instr.mapWires e)).map eraseInstr=place f (gs.map eraseInstr) := by
  simp only [place,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i _
  exact erase_mapWires e f he i









@[simp] theorem erase_compileCommand {n : ℕ} (c : BooleanCircuits.Command n) :
    eraseInstr (BooleanCircuits.compileCommand c)=compileCommand (eraseCommand c) := by
  cases c with
  | flip t => rfl
  | copy a t h => rfl
  | conj a b t ha hb =>
    by_cases h : a=b
    · subst b
      simp only [BooleanCircuits.compileCommand,dif_pos rfl,eraseCommand,compileCommand,if_pos rfl]
      rfl
    · have hv : a.val≠b.val := fun hv=>h (Fin.ext hv)
      simp only [BooleanCircuits.compileCommand,dif_neg h,eraseCommand,compileCommand,if_neg hv]
      rfl

@[simp] theorem erase_compile {n : ℕ} (p : List (BooleanCircuits.Command n)) :
    (BooleanCircuits.compile p).map eraseInstr=compile (p.map eraseCommand) := by
  simp [BooleanCircuits.compile,compile,List.map_map,Function.comp_def]











@[simp] theorem erase_andGates {r n : ℕ} (L : ControlCircuits.AndLayout r n) :
    (ControlCircuits.andGates L).map eraseInstr=andGates (eraseAnd L) := by
  rw [ControlCircuits.andGates_eq_map]
  simp only [List.map_append,List.map_cons,List.map_nil,erase_x,List.map_map]
  rfl

@[simp] theorem erase_multiControlledX {r n : ℕ} (L : ControlCircuits.AndLayout r n)
    (target : Fin n) (h : ∀j,target≠L.flags j) :
    (ControlCircuits.multiControlledX L target h).map eraseInstr=multiControlledX (eraseAnd L) target.val := by
  simp only [ControlCircuits.multiControlledX,ReversibleGadgets.computeUseUncompute,
    List.map_append,List.map_reverse,erase_andGates,List.map_cons,List.map_nil,erase_cn]
  rfl







@[simp] theorem erase_normalizePrefix {r n : ℕ} (L : ControlCircuits.AndLayout r n)
    (p : Fin r → Bool) (t : ℕ) (ht : t≤r) :
    (EqualityCircuits.normalizePrefixGates L p t ht).map eraseInstr=normalizePrefix (eraseAnd L) p t ht := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [EqualityCircuits.normalizePrefixGates,normalizePrefix,List.map_append,ih (by omega)]
    split <;> rfl

@[simp] theorem erase_normalize {r n : ℕ} (L : ControlCircuits.AndLayout r n) (p : Fin r → Bool) :
    (EqualityCircuits.normalizeGates L p).map eraseInstr=normalize (eraseAnd L) p :=
  erase_normalizePrefix L p r le_rfl

@[simp] theorem erase_patternControlledX {r n : ℕ} (L : ControlCircuits.AndLayout r n)
    (p : Fin r → Bool) (target : Fin n) (h : ∀j,target≠L.flags j) :
    (EqualityCircuits.patternControlledX L p target h).map eraseInstr=
      patternControlledX (eraseAnd L) p target.val := by
  simp only [EqualityCircuits.patternControlledX,ReversibleGadgets.computeUseUncompute,
    List.map_append,List.map_reverse,erase_normalize,erase_multiControlledX]
  rfl

end QMAPerfectCompleteness.Main.RawG2

end

/- Inline helpers retained from Solutions.RawControlGadgets. -/
section


/-! Executable bounded-loop control, comparison, clock and phase circuit templates. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.RawG2
open RawEncoding





@[simp] theorem erase_prefixLayout {r n : ℕ} (L : ControlCircuits.AndLayout r n) (t : ℕ) (ht : t≤r) :
    eraseAnd (ComparisonCircuits.prefixLayout L t ht)=prefixLayout (eraseAnd L) t ht := rfl
@[simp] theorem erase_reverseLayout {r n : ℕ} (L : ControlCircuits.AndLayout r n) :
    eraseAnd (ComparisonCircuits.reverseLayout L)=reverseLayout (eraseAnd L) := rfl









@[simp] theorem erase_stageGates {r n : ℕ} (L : ControlCircuits.AndLayout r n)
    (p : Fin r → Bool) (target : Fin n) (h : ∀j,target≠L.flags j) (t : ℕ) (ht : t<r) :
    (ComparisonCircuits.stageGates L p target h t ht).map eraseInstr=
      stageGates (eraseAnd L) p target.val t ht := by
  unfold ComparisonCircuits.stageGates stageGates
  split <;> simp only [erase_patternControlledX,erase_prefixLayout,List.map_nil]

@[simp] theorem erase_comparePrefix {r n : ℕ} (L : ControlCircuits.AndLayout r n)
    (p : Fin r → Bool) (target : Fin n) (h : ∀j,target≠L.flags j) (t : ℕ) (ht : t≤r) :
    (ComparisonCircuits.comparePrefixGates L p target h t ht).map eraseInstr=
      comparePrefix (eraseAnd L) p target.val t ht := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [ComparisonCircuits.comparePrefixGates,comparePrefix,List.map_append,ih (by omega),erase_stageGates]

@[simp] theorem erase_compareGates {r n : ℕ} (L : ControlCircuits.AndLayout r n)
    (p : Fin r → Bool) (target : Fin n) (h : ∀j,target≠L.flags j) :
    (ComparisonCircuits.compareGates L p target h).map eraseInstr=compareGates (eraseAnd L) p target.val := by
  simp only [ComparisonCircuits.compareGates,compareGates,erase_comparePrefix,erase_reverseLayout]

@[simp] theorem erase_compareNatGates {r n : ℕ} (L : ControlCircuits.AndLayout r n)
    (a : ℕ) (target : Fin n) (h : ∀j,target≠L.flags j) :
    (ComparisonCircuits.compareNatGates L a target h).map eraseInstr=compareNatGates (eraseAnd L) a target.val := by
  unfold ComparisonCircuits.compareNatGates compareNatGates
  split <;> simp only [erase_compareGates,List.map_cons,List.map_nil,erase_x]







@[simp] theorem erase_incrementStep {r n : ℕ} (L : ControlCircuits.AndLayout (r+1) n)
    (t : ℕ) (ht : t<r) :
    (ClockCircuits.incrementStepGates L t ht).map eraseInstr=incrementStep (eraseAnd L) t ht := by
  simp only [ClockCircuits.incrementStepGates,incrementStep,erase_multiControlledX,erase_prefixLayout]
  rfl

@[simp] theorem erase_incrementPrefix {r n : ℕ} (L : ControlCircuits.AndLayout (r+1) n)
    (t : ℕ) (ht : t≤r) :
    (ClockCircuits.incrementPrefixGates L t ht).map eraseInstr=incrementPrefix (eraseAnd L) t ht := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [ClockCircuits.incrementPrefixGates,incrementPrefix,List.map_append,erase_incrementStep,ih (by omega)]

@[simp] theorem erase_increment {r n : ℕ} (L : ControlCircuits.AndLayout (r+1) n) :
    (ClockCircuits.controlledIncrementGates L).map eraseInstr=increment (eraseAnd L) :=
  erase_incrementPrefix L r le_rfl




@[simp] theorem erase_phase {n : ℕ} (e : Fin 2 ↪ Fin n) :
    (ReversibleGadgets.phaseZAt e).map eraseInstr=phase (e 0).val (e 1).val := rfl
@[simp] theorem erase_tripleControlledX {n : ℕ} (e : Fin 5 ↪ Fin n) :
    (ReversibleGadgets.tripleControlledXAt e).map eraseInstr=tripleControlledX (fun j=>(e j).val) := rfl





end QMAPerfectCompleteness.Main.RawG2

end

/- Inline helpers retained from Solutions.BlockCompiler. -/
section


/-! Concrete paper block-compiler scaffolds. Circuit data depend only on layout and certificate. -/

open Matrix
namespace QMAPerfectCompleteness.Main.BlockCompiler
open ReversibleGadgets ControlCircuits EqualityCircuits ComparisonCircuits ClockCircuits





namespace CleanProgram





end CleanProgram

namespace Layout





















































































































































































theorem midProgram_gates (D : Layout) : D.midProgram.gates = D.mid := by
  simp only [midProgram, CleanProgram.append, CleanProgram.reverseOfInvolution,
    clockBelowProgram, forwardFlagProgram, mid, List.append_assoc]



































































end Layout











end QMAPerfectCompleteness.Main.BlockCompiler

end

/- Inline helpers retained from Solutions.RawArithmeticGadgets. -/
section


/-! Executable linear ripple circuits, with exact erasure of their proved typed counterparts. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QMAPerfectCompleteness.Main.RawG2
open RawEncoding











@[simp] theorem erase_borrowCommands {n : ℕ} (e : Fin 5 ↪ Fin n) :
    (VariableComparison.borrowCommands e).map eraseCommand=borrowCommands (fun j=>(e j).val) := rfl



@[simp] theorem erase_borrowPrefix {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (t : ℕ) (ht : t≤r) :
    (VariableComparison.borrowChain e t ht).map eraseCommand=borrowPrefix (eraseBorrow e) t ht := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [VariableComparison.borrowChain,List.map_append,ih (by omega),erase_borrowCommands]
    apply congrArg (fun q : Fin 5 → ℕ => borrowPrefix (eraseBorrow e) t (by omega) ++ borrowCommands q)
    funext j
    fin_cases j <;> try rfl

@[simp] theorem erase_comparator {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n)
    (target : Fin n) (hout : ∀j,target≠e j) :
    (VariableComparison.comparatorGates e target hout).map eraseInstr=comparator (eraseBorrow e) target.val := by
  simp only [VariableComparison.comparatorGates,ReversibleGadgets.computeUseUncompute,
    List.map_append,List.map_reverse,erase_compile,erase_borrowPrefix,List.map_cons,List.map_nil,erase_cn]
  rfl



@[simp] theorem erase_swapBorrow {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) :
    eraseBorrow (VariableEquality.swapInputs e)=swapBorrow (eraseBorrow e) := by
  simp only [eraseBorrow,swapBorrow,VariableEquality.swap_left,VariableEquality.swap_right,
    VariableEquality.swap_carry,VariableEquality.swap_temp]



@[simp] theorem erase_equality {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n)
    (target : Fin n) (hout : ∀j,target≠e j) :
    (VariableEquality.gates e target hout).map eraseInstr=equality (eraseBorrow e) target.val := by
  simp only [VariableEquality.gates,VariableEquality.program,BlockCompiler.CleanProgram.append,
    VariableEquality.comparisonProgram,VariableEquality.swappedProgram,VariableEquality.flipProgram,
    List.map_append,erase_comparator,erase_swapBorrow,List.map_cons,List.map_nil,erase_x]
  rfl















@[simp] theorem erase_carryCommands {n : ℕ} (e : Fin 5 ↪ Fin n) :
    (VariableAddition.carryCommands e).map eraseCommand=carryCommands (fun j=>(e j).val) := rfl

@[simp] theorem erase_carryPrefix {r n : ℕ} (L : VariableAddition.Layout r n) (t : ℕ) (ht : t≤r) :
    (L.carryPrefix t ht).map eraseCommand=carryPrefix (eraseAddition L) t ht := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [VariableAddition.Layout.carryPrefix,carryPrefix,List.map_append,ih (by omega),erase_carryCommands]
    rfl



@[simp] theorem erase_additionCommands {r n : ℕ} (L : VariableAddition.Layout r n) :
    L.commands.map eraseCommand=additionCommands (eraseAddition L) := by
  simp only [VariableAddition.Layout.commands,additionCommands,VariableAddition.Layout.sumCommands,
    List.map_append,List.map_reverse,erase_carryPrefix,List.map_flatMap]
  rfl



end QMAPerfectCompleteness.Main.RawG2

end

/- Inline helpers retained from Solutions.DynamicRangeLayout. -/
section


/-! Disjoint source/scratch register constructors for the dynamic range comparator scaffold. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QMAPerfectCompleteness.Main.DynamicBlockCompiler
open VariableComparison





namespace RangeWires
variable {n r : ℕ} (W : RangeWires n r)



lemma comparator_left (t : Fin 3) (i : Fin r) : leftWire (W.comparator t) i = W.index i := by
  change Fin.append (Fin.append W.index (W.thresholds t)) W.scratch
    (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨i.val,by have := i.isLt; omega⟩) = _
  have he : (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨i.val,by have := i.isLt; omega⟩) =
      Fin.castAdd (r+2) (Fin.castAdd r i) := Fin.ext rfl
  rw [he,Fin.append_left,Fin.append_left]

lemma comparator_right (t : Fin 3) (i : Fin r) : rightWire (W.comparator t) i = W.thresholds t i := by
  change Fin.append (Fin.append W.index (W.thresholds t)) W.scratch
    (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨r+i.val,by have := i.isLt; omega⟩) = _
  have he : (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨r+i.val,by have := i.isLt; omega⟩) =
      Fin.castAdd (r+2) (Fin.natAdd r i) := Fin.ext rfl
  rw [he,Fin.append_left,Fin.append_right]

lemma comparator_carry (t : Fin 3) (i : Fin (r+1)) :
    carryWire (W.comparator t) i = W.scratch (Fin.castAdd 1 i) := by
  change Fin.append (Fin.append W.index (W.thresholds t)) W.scratch
    (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨2*r+i.val,by have := i.isLt; omega⟩) = _
  have he : (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨2*r+i.val,by have := i.isLt; omega⟩) =
      Fin.natAdd (r+r) (Fin.castAdd 1 i) := Fin.ext (by
        change 2*r+i.val = r+r+i.val
        omega)
  rw [he,Fin.append_right]

lemma comparator_temp (t : Fin 3) : tempWire (W.comparator t) = W.scratch (Fin.last (r+1)) := by
  change Fin.append (Fin.append W.index (W.thresholds t)) W.scratch
    (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨3*r+1,by omega⟩) = _
  have he : (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨3*r+1,by omega⟩) =
      Fin.natAdd (r+r) (Fin.last (r+1)) := Fin.ext (by simp; omega)
  rw [he,Fin.append_right]







end RangeWires
end QMAPerfectCompleteness.Main.DynamicBlockCompiler

end

/- Inline helpers retained from Solutions.CertificateHistoryPrograms. -/
section


/-! Clean compute/use/uncompute of the variable certificate history predicate. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateHistoryPrograms
open BlockCompiler ReversibleGadgets VariableHistoryEquality

namespace Layout
variable {m c n : ℕ} (L : VariableHistoryEquality.Layout m c n)










end Layout



namespace ClosingLayout
variable {m c n : ℕ} (L : ClosingLayout m c n)


















lemma gates_eq : L.gates = L.history.gates ++ [toffoliAt L.targets] ++ L.history.gates.reverse := rfl







end ClosingLayout
end QMAPerfectCompleteness.Main.CertificateHistoryPrograms

end

/- Inline helpers retained from Solutions.CyclicRawLayout. -/
section


/-! Executable scalar metadata and affine physical addresses for the actual cyclic compiler. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.CyclicRaw
open RawEncoding CertificateMasterLayout





namespace Meta



































end Meta





@[simp] theorem m_meta (V : Verifier gatesG2) : (params V).m=V.proofQubits := by simp only [params,ofRaw_erase]
@[simp] theorem a_meta (V : Verifier gatesG2) : (params V).a=V.ancillaQubits := by simp only [params,ofRaw_erase]
@[simp] theorem c_meta (V : Verifier gatesG2) : (params V).c=BlockCircuit.clockWires V := by simp only [params,ofRaw_erase]
@[simp] theorem k_meta (V : Verifier gatesG2) : (params V).k=indexQubits V := by simp only [params,ofRaw_erase]
@[simp] theorem countproof_meta (V : Verifier gatesG2) : (params V).proof=CertificateCoordinates.proofQubits V := by simp only [params,ofRaw_erase]; rfl

@[simp] theorem r_meta (V : Verifier gatesG2) : (params V).r=r V := by simp only [params,ofRaw_erase]; rfl
@[simp] theorem oldWork_meta (V : Verifier gatesG2) : (params V).oldWork=oldWork V := by simp only [params,ofRaw_erase]; rfl

@[simp] theorem work_meta (V : Verifier gatesG2) : (params V).work=work V := by simp only [params,ofRaw_erase]; rfl
@[simp] theorem body_meta (V : Verifier gatesG2) : (params V).body=BlockCircuit.bodyWires V := by simp only [params,ofRaw_erase]; rfl





@[simp] theorem word_meta (V : Verifier gatesG2) (d : Fin 6) (j : Fin (r V)) :
    (prepWord V d j).val=(params V).word d.val j.val := by
  change BlockCircuit.bodyWires V+oldWork V+(j.val+r V*d.val) =
    (params V).body+(params V).oldWork+(d.val*(params V).r+j.val)
  rw [body_meta,oldWork_meta,r_meta]
  ac_rfl






@[simp] theorem certificate_meta (V : Verifier gatesG2) (s : Fin 2) (j : Fin (k V)) :
    (certificate V s j).val=(params V).certificate s.val j.val := by
  simp only [params,ofRaw_erase]
  change BlockCircuit.bodyWires V+work V+V.proofQubits+(j.val+k V*s.val) = _
  change _ = BlockCircuit.bodyWires V+work V+V.proofQubits+(s.val*k V+j.val)
  simp only [Nat.mul_comm,Nat.add_comm]

@[simp] theorem permute_meta (V : Verifier gatesG2) (j : Fin (total V)) :
    (CertificateVerifierLayout.wireEquiv V (work V) j).val=(params V).permute j.val := by
  simp only [CertificateVerifierLayout.wireEquiv,Equiv.trans_apply,finCongr_apply_coe,
    CertificateVerifierLayout.reorder]
  simp only [Meta.permute,k_meta,c_meta,m_meta,a_meta,work_meta,countproof_meta]
  rfl

end QMAPerfectCompleteness.Main.CyclicRaw

end

/- Inline helpers retained from Solutions.RawThresholdGadgets. -/
section


/-! Executable certificate threshold preparation, independent of quantum matrix data. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.RawG2
open RawEncoding








lemma addition_ext {r : ℕ} (L M : AdditionLayout r)
    (hl : ∀j,L.left j=M.left j) (hr : ∀j,L.right j=M.right j)
    (hc : ∀j,L.carry j=M.carry j) (ho : ∀j,L.output j=M.output j) (hp : L.temp=M.temp) : L=M := by
  cases L with
  | mk a b c d e =>
    cases M with
    | mk A B C D E =>
      have ha : a=A := funext hl
      have hb : b=B := funext hr
      have hc' : c=C := funext hc
      have hd : d=D := funext ho
      cases ha; cases hb; cases hc'; cases hd
      cases hp
      rfl

@[simp] theorem erase_threeLayout {k n : ℕ} (L : ThresholdPreparation.Layout k n) :
    eraseAddition L.three=threeLayout (eraseThreshold L) := by
  apply addition_ext
  · intro j; exact congrArg Fin.val (L.three_left j)
  · intro j; exact congrArg Fin.val (L.three_right j)
  · intro j; exact congrArg Fin.val (L.three_carry j)
  · intro j; exact congrArg Fin.val (L.three_output j)
  · exact congrArg Fin.val L.three_temp

@[simp] theorem erase_upperLayout {k n : ℕ} (L : ThresholdPreparation.Layout k n) :
    eraseAddition L.upper=upperLayout (eraseThreshold L) := by
  apply addition_ext
  · intro j; exact congrArg Fin.val (L.upper_left j)
  · intro j; exact congrArg Fin.val (L.upper_right j)
  · intro j; exact congrArg Fin.val (L.upper_carry j)
  · intro j; exact congrArg Fin.val (L.upper_output j)
  · exact congrArg Fin.val L.upper_temp







@[simp] theorem erase_thresholdCopies {k n : ℕ} (L : ThresholdPreparation.Layout k n) :
    L.copies.map eraseCommand=thresholdCopies (eraseThreshold L) := by
  simp only [ThresholdPreparation.Layout.copies,RegisterCopies.commands,List.map_map,
    thresholdCopies,Function.comp_def]
  rfl

@[simp] theorem erase_thresholdCommands {k n : ℕ} (L : ThresholdPreparation.Layout k n) :
    L.commands.map eraseCommand=thresholdCommands (eraseThreshold L) := by
  simp only [ThresholdPreparation.Layout.commands,thresholdCommands,List.map_append,
    erase_thresholdCopies,erase_additionCommands,erase_threeLayout,erase_upperLayout]

@[simp] theorem erase_threshold {k n : ℕ} (L : ThresholdPreparation.Layout k n) :
    L.gates.map eraseInstr=threshold (eraseThreshold L) := by
  rw [ThresholdPreparation.Layout.gates,erase_compile,erase_thresholdCommands]
  rfl

end QMAPerfectCompleteness.Main.RawG2

end

/- Inline helpers retained from Solutions.RawCertificateGadgets. -/
section


/-! Executable certificate-control templates and literal typed-erasure proofs. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace QMAPerfectCompleteness.Main.RawG2
open RawEncoding







@[simp] theorem erase_history {m c n : ℕ} (L : VariableHistoryEquality.Layout m c n) :
    L.gates.map eraseInstr=history (eraseHistory L) := by
  simp only [VariableHistoryEquality.Layout.gates,VariableHistoryEquality.Layout.program,
    BlockCompiler.CleanProgram.append,BlockCompiler.CleanProgram.reverseOfInvolution,
    VariableHistoryEquality.Layout.equalityProgram,VariableHistoryEquality.Layout.clockProgram,
    VariableHistoryEquality.Layout.useProgram,List.map_append,List.map_reverse,
    erase_equality,erase_patternControlledX,List.map_cons,List.map_nil,erase_tof]
  rfl



@[simp] theorem erase_closing {m c n : ℕ} (L : CertificateHistoryPrograms.ClosingLayout m c n) :
    L.gates.map eraseInstr=closing (eraseHistory L.history) L.range.val L.flag.val := by
  rw [L.gates_eq]
  simp only [List.map_append,List.map_reverse,erase_history,List.map_cons,List.map_nil,erase_tof]
  rfl







@[simp] theorem erase_readout {r n : ℕ} (L : CertificateReadout.Layout r n) :
    L.gates.map eraseInstr=readout (eraseReadout L) := by
  simp only [CertificateReadout.Layout.gates,CertificateReadout.Layout.program,
    BlockCompiler.CleanProgram.append,BlockCompiler.CleanProgram.reverseOfInvolution,
    CertificateReadout.Layout.zeroProgram,CertificateReadout.Layout.flagProgram,
    List.map_append,List.map_reverse,erase_patternControlledX,erase_compile]
  rfl









@[simp] theorem erase_andNot {r n : ℕ} (L : DynamicBlockCompiler.RangeLayout n r)
    (a b c : Fin 6) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    (L.andNotProgram a b c hab hac hbc).gates.map eraseInstr=andNot (L.tags a).val (L.tags b).val (L.tags c).val := by
  simp only [DynamicBlockCompiler.RangeLayout.andNotProgram,erase_compile]
  rfl

@[simp] theorem erase_range {r n : ℕ} (L : DynamicBlockCompiler.RangeLayout n r) :
    L.gates.map eraseInstr=range (eraseRange L) := by
  simp only [DynamicBlockCompiler.RangeLayout.gates,DynamicBlockCompiler.RangeLayout.program,
    BlockCompiler.CleanProgram.append,List.map_append,erase_andNot,
    DynamicBlockCompiler.RangeLayout.compareProgram,erase_comparator]
  rfl







@[simp] theorem erase_criteria {k n : ℕ} (L : CertificateValidity.Layout k n) :
    L.gates.map eraseInstr=criteria (eraseValidity L) := by
  simp only [CertificateValidity.Layout.gates,CertificateValidity.Layout.program,
    BlockCompiler.CleanProgram.append,List.map_append,CertificateValidity.Layout.constProgram,
    Bool.false_eq_true,if_false,if_true,erase_compareNatGates,
    CertificateValidity.Layout.flipProgram,List.map_cons,List.map_nil,erase_x,
    CertificateValidity.Layout.varProgram,erase_comparator]
  rfl





@[simp] theorem erase_validity {k n : ℕ} (L : CertificateValidity.Layout k n) (hk : 3≤k)
    (out : Fin n) (hot : ∀t,out≠L.tags t) (hoa : ∀j,out≠L.a.flags j)
    (hob : ∀j,out≠L.b.flags j) (hoc : ∀j,out≠L.cmp j) :
    (L.validProgram hk out hot hoa hob hoc).gates.map eraseInstr=validity (eraseValidity L) out.val := by
  change (L.gates ++ (L.outputProgram hk out hot hoa hob hoc).gates).map eraseInstr = _
  rw [List.map_append,erase_criteria]
  unfold CertificateValidity.Layout.outputProgram
  rw [erase_multiControlledX]
  congr 2
  change AndLayout.mk (fun j=>(L.tags j).val) _ = AndLayout.mk (fun j=>(L.tags j).val) _
  apply congrArg (AndLayout.mk (fun j=>(L.tags j).val))
  funext j
  change (L.a.flags ⟨j.val,by omega⟩).val=(L.a.flags ⟨min j.val (k+2),by omega⟩).val
  have hj := j.isLt
  simp only [min_eq_left (by omega : j.val≤k+2)]

end QMAPerfectCompleteness.Main.RawG2

end



/-! Literal raw-code correspondence for the coherent certificate compiler. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace QMAPerfectCompleteness.Main.CyclicRaw
end QMAPerfectCompleteness.Main.CyclicRaw
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CyclicRaw
open RawEncoding RawG2 CertificateMasterLayout


@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.params_eq_source (V : Verifier gatesG2) : params V=sourceMeta V := ofRaw_erase V

@[ext] theorem QMAPerfectCompleteness.Main.CyclicRaw.and_ext {r : ℕ} (L M : RawG2.AndLayout r)
    (hc : ∀j,L.controls j=M.controls j) (hf : ∀j,L.flags j=M.flags j) : L=M := by
  cases L; cases M
  simp only [AndLayout.mk.injEq]
  exact ⟨funext hc,funext hf⟩

@[ext] theorem QMAPerfectCompleteness.Main.CyclicRaw.borrow_ext {r : ℕ} (L M : RawG2.BorrowLayout r)
    (ha : ∀j,L.left j=M.left j) (hb : ∀j,L.right j=M.right j)
    (hc : ∀j,L.carry j=M.carry j) (hp : L.temp=M.temp) : L=M := by
  cases L; cases M
  simp only [BorrowLayout.mk.injEq]
  exact ⟨funext ha,funext hb,funext hc,hp⟩

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.source_word (V : Verifier gatesG2) (d : Fin 6) (j : Fin (r V)) :
    (prepWord V d j).val=(sourceMeta V).word d.val j.val := by
  simpa only [params_eq_source] using word_meta V d j
@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.source_certificate (V : Verifier gatesG2) (s : Fin 2) (j : Fin (k V)) :
    (certificate V s j).val=(sourceMeta V).certificate s.val j.val := by
  simpa only [params_eq_source] using certificate_meta V s j

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.thresholdLayout_raw (V : Verifier gatesG2) :
    eraseThreshold (CertificatePreparation.thresholdLayout V)=(sourceMeta V).thresholds := by
  change ThresholdLayout.mk _ _ _ _ = ThresholdLayout.mk _ _ _ _
  congr 1
  · funext d j
    exact source_certificate V d j
  · funext d j
    exact source_word V d j

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.prepGates_raw (V : Verifier gatesG2) :
    (CertificatePreparation.prepGates V).map eraseInstr=(sourceMeta V).prepGates := by
  rw [CertificatePreparation.prepGates,erase_threshold,thresholdLayout_raw]
  rfl

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.erase_wires_comparator {n r : ℕ} (W : DynamicBlockCompiler.RangeWires n r) (d : Fin 3) :
    eraseBorrow (W.comparator d)=
      ⟨fun j=>(W.index j).val,fun j=>(W.thresholds d j).val,
        fun j=>(W.scratch (Fin.castAdd 1 j)).val,(W.scratch (Fin.last (r+1))).val⟩ := by
  apply borrow_ext
  · intro j; exact congrArg Fin.val (W.comparator_left d j)
  · intro j; exact congrArg Fin.val (W.comparator_right d j)
  · intro j; exact congrArg Fin.val (W.comparator_carry d j)
  · exact congrArg Fin.val (W.comparator_temp d)



@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.rangeGates_raw (V : Verifier gatesG2) :
    (CertificateRangeCircuit.gates V).map eraseInstr=(sourceMeta V).rangeGates := by
  rw [CertificateRangeCircuit.gates,erase_range,rangeLayout_raw]
  rfl

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.validityLayout_raw (V : Verifier gatesG2) :
    eraseValidity (CertificateValidityCircuit.layout V)=(sourceMeta V).validityLayout := by
  change ValidityLayout.mk _ _ _ _ = ValidityLayout.mk _ _ _ _
  congr 1
  · apply and_ext
    · intro j; exact source_word V 0 j
    · intro j; rfl
  · apply and_ext
    · intro j; exact source_word V 2 j
    · intro j; rfl
  · change eraseBorrow ((CertificateValidityCircuit.comparatorWires V).comparator 0)=_
    rw [erase_wires_comparator]
    apply borrow_ext
    · intro j; exact source_word V 0 j
    · intro j; exact source_word V 3 j
    · intro j; rfl
    · change BlockCircuit.bodyWires V+(oldWork V+6*r V)+(r V+1)=
        BlockCircuit.bodyWires V+(oldWork V+6*r V+(k V+3))
      dsimp only [r,k]
      omega

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.validGates_raw (V : Verifier gatesG2) :
    (CertificateValidityCircuit.gates V).map eraseInstr=(sourceMeta V).validGates := by
  unfold CertificateValidityCircuit.gates CertificateValidityCircuit.program
  rw [erase_validity,validityLayout_raw]
  rfl

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.prefixGates_raw (V : Verifier gatesG2) :
    (CertificatePreparation.prefixGates V).map eraseInstr=(sourceMeta V).prefixGates := by
  simp only [CertificatePreparation.prefixGates,List.map_append,prepGates_raw,validGates_raw]
  rfl



@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.closingGates_raw (V : Verifier gatesG2) :
    (CertificateClosingCircuit.gates V).map eraseInstr=
      RawG2.closing (sourceMeta V).historyLayout ((sourceMeta V).tag 4) (sourceMeta V).flag := by
  rw [CertificateClosingCircuit.gates,erase_closing]
  change RawG2.closing (eraseHistory (CertificateMasterLayout.historyLayout V)) _ _ = _
  rw [historyLayout_raw]
  rfl

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.place_id (gs : List RawEncoding.Instruction) : RawG2.place id gs=gs := by
  simp [RawG2.place]

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.hadamards_raw (V : Verifier gatesG2) :
    (CertificateHadamardCoordinates.gates V (work V)).map eraseInstr=(sourceMeta V).indexH := by
  unfold CertificateHadamardCoordinates.gates IndexHadamards.pairedHadamards
    Meta.indexH RawG2.pairedHadamards
  simp only [List.map_map]
  apply List.map_congr_left
  intro j _
  rfl

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.forward_raw (V : Verifier gatesG2) :
    (CertificateVerifierCoordinates.forward V (work V)).map eraseInstr=
      RawG2.place (sourceMeta V).verifier (eraseVerifier V).gates := by
  unfold CertificateVerifierCoordinates.forward BlockCircuit.forwardGates
  rw [erase_mapGates _ id (fun _=>rfl),place_id]
  exact erase_mapGates _ (sourceMeta V).verifier (fun _=>rfl) V.gates

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.backward_raw (V : Verifier gatesG2) :
    (CertificateVerifierCoordinates.backward V (work V)).map eraseInstr=
      RawG2.place (sourceMeta V).verifier (eraseVerifier V).gates.reverse := by
  unfold CertificateVerifierCoordinates.backward BlockCircuit.backwardGates
  rw [erase_mapGates _ id (fun _=>rfl),place_id]
  rw [List.map_reverse,BlockCircuit.forwardGates,erase_mapGates _ (sourceMeta V).verifier (fun _=>rfl)]
  simp only [RawG2.place,List.map_reverse]
  rfl

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.mid_raw (V : Verifier gatesG2) :
    (CertificateOldPrograms.midProgram V).gates.map eraseInstr=(sourceMeta V).mid := by
  unfold CertificateOldPrograms.midProgram BlockCompiler.CleanProgram.mapWires
  rw [erase_mapGates _ id (fun _=>rfl),place_id,BlockCompiler.Layout.midProgram_gates]
  simp only [BlockCompiler.Layout.mid,List.map_append,List.map_reverse,
    BlockCompiler.Layout.clockBelowGates,erase_compareNatGates,erase_tripleControlledX]
  rfl

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.increment_raw (V : Verifier gatesG2) :
    (CertificateOldPrograms.incrementProgram V).gates.map eraseInstr=
      RawG2.increment (sourceMeta V).incrementLayout := by
  unfold CertificateOldPrograms.incrementProgram BlockCompiler.CleanProgram.mapWires
  rw [erase_mapGates _ id (fun _=>rfl),place_id]
  change (ClockCircuits.controlledIncrementGates (BlockCompiler.layoutOf V).incrementLayout).map eraseInstr=_
  rw [erase_increment]
  apply congrArg RawG2.increment
  apply and_ext
  · intro j
    refine Fin.cases ?_ (fun t=>?_) j
    · rfl
    · change indexQubits V+t.val = if t.val+1=0 then (sourceMeta V).tag 5 else indexQubits V+(t.val+1-1)
      rw [if_neg (by omega)]
      omega
  · intro j; rfl

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.identity_raw (V : Verifier gatesG2) :
    (CertificateOldPrograms.identityFlagProgram V).gates.map eraseInstr=
      [RawG2.cn ((sourceMeta V).tag 0) (sourceMeta V).flag] := by
  unfold CertificateOldPrograms.identityFlagProgram BlockCompiler.CleanProgram.mapWires
  rw [erase_mapGates _ id (fun _=>rfl),place_id]
  rfl

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.phase_raw (V : Verifier gatesG2) :
    (CertificateOldPrograms.phaseGates V).map eraseInstr=
      RawG2.phase ((sourceMeta V).tag 5) ((sourceMeta V).tag 9) := by
  unfold CertificateOldPrograms.phaseGates
  rw [erase_mapGates _ id (fun _=>rfl),place_id,erase_phase]
  rfl

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.post_raw (V : Verifier gatesG2) :
    (CertificateBlockCorrectness.postGates V).map eraseInstr=(sourceMeta V).post := by
  simp only [CertificateBlockCorrectness.postGates,List.map_append,closingGates_raw,
    identity_raw,increment_raw,phase_raw,Meta.post]

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.readoutLayout_raw (V : Verifier gatesG2) :
    eraseReadout (readoutLayout V)=(sourceMeta V).readoutLayout := by
  change ReadoutLayout.mk _ _ = ReadoutLayout.mk _ _
  congr 1
  funext j
  fin_cases j
  · change BlockCircuit.bodyWires V+(oldWork V+prepWork V+7)=
        BlockCircuit.bodyWires V+(oldWork V+prepWork V+2)+5
    omega
  · rfl
  · rfl

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.readoutGates_raw (V : Verifier gatesG2) :
    (readoutGates V).map eraseInstr=RawG2.readout (sourceMeta V).readoutLayout := by
  rw [readoutGates,erase_readout,readoutLayout_raw]


@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.block_raw (V : Verifier gatesG2) :
    (CertificateBlockCorrectness.gates V).map eraseInstr=(sourceMeta V).block (eraseVerifier V).gates := by
  simp only [CertificateBlockCorrectness.gates,CertificateBlockCorrectness.selectGates,
    List.map_append,List.map_reverse,hadamards_raw,rangeGates_raw,forward_raw,backward_raw,
    mid_raw,post_raw,Meta.block]

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.gates_raw (V : Verifier gatesG2) :
    (CyclicVerifier.gates V).map eraseInstr=(sourceMeta V).gates (eraseVerifier V).gates := by
  simp only [CyclicVerifier.gates,List.map_append,prefixGates_raw,block_raw,readoutGates_raw,
    Meta.gates,CertificateEtaTransport.gates,List.map_cons,List.map_nil,erase_x]
  rfl

theorem QMAPerfectCompleteness.Main.CyclicRaw.circuit_ext (A B : RawEncoding.Circuit)
    (hm : A.proofQubits=B.proofQubits) (ha : A.ancillaQubits=B.ancillaQubits)
    (ho : A.output=B.output) (hg : A.gates=B.gates) : A=B := by
  cases A; cases B
  simp only [RawEncoding.Circuit.mk.injEq]
  exact ⟨hm,ha,ho,hg⟩

/-- The executable raw compiler emits precisely the already-verified coherent verifier. -/
theorem solution (V : Verifier gatesG2) :
    compileRaw (eraseVerifier V)=eraseVerifier (CyclicVerifier.compileVerifier V) := by
  unfold compileRaw
  rw [ofRaw_erase]
  refine circuit_ext _ _ rfl rfl ?_ ?_
  · change (sourceMeta V).permute (sourceMeta V).readoutOutput =
      (CertificateVerifierLayout.wireEquiv V (work V) (readoutLayout V).output).val
    rw [permute_meta,params_eq_source]
    congr 1
  · change RawG2.place (sourceMeta V).permute ((sourceMeta V).gates (eraseVerifier V).gates)=_
    change _=((CyclicVerifier.gates V).map (Instr.mapWires (CertificateVerifierLayout.wireEquiv V (work V)).toEmbedding)).map eraseInstr
    rw [erase_mapGates _ (sourceMeta V).permute (fun j=>by
      change (CertificateVerifierLayout.wireEquiv V (work V) j).val=(sourceMeta V).permute j.val
      simpa only [params_eq_source] using permute_meta V j),gates_raw]
