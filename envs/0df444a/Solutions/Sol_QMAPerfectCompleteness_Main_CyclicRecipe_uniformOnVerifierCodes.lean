-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CyclicRecipe.uniformOnVerifierCodes
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:55:06.81123+00:00
-- url     : https://prove2.me/submissions/9d3d420d-0838-4888-9117-ce02333b6d0b

/- Generated from Solutions.CyclicUniformity by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
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
import Definitions.Def_QMAPerfectCompleteness_Proof_BoundedWriterTM
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitExprTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitProvisionalWriter
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClassTransport
import Definitions.Def_QMAPerfectCompleteness_Proof_ClearStacksTM
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentAcceptance
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ConditionalWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CountedWriterLoops
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicClockMetadata
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicClockPrefixTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicFullMetadata
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataIO
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicMetadataTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicProvisionalCode
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRecipeRealization
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicVerifier
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_FinitePlanCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_HTEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_HTPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_InstructionBuffersTM
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawArithmeticGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCertificateGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RawControlGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawThresholdGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeCompositeWriters
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeLeafWriter
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeNormalization
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeSerializerContinuation
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeSerializerSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeSerializerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeVerifierContext
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeWriterContext
import Definitions.Def_QMAPerfectCompleteness_Proof_RecountGatesCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_RecountGatesTM
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_SourceBuffersTM
import Definitions.Def_QMAPerfectCompleteness_Proof_SourceInstructionMapper
import Definitions.Def_QMAPerfectCompleteness_Proof_SourceWriter
import Definitions.Def_QMAPerfectCompleteness_Proof_SourceWriterBounds
import Definitions.Def_QMAPerfectCompleteness_Proof_SourceWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_StackEmbedding
import Definitions.Def_QMAPerfectCompleteness_Proof_StackTransfers
import Definitions.Def_QMAPerfectCompleteness_Proof_StreamWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryDispatch
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryEvaluator
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryFieldCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryMetadataArithmetic
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerPhases
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryStackOps
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding
import Theorems.Thm_QMAPerfectCompleteness_Main_CircuitRecipe_Gadgets_eval_compareBits
import Theorems.Thm_QMAPerfectCompleteness_Main_CyclicRaw_historyLayout_raw
import Theorems.Thm_QMAPerfectCompleteness_Main_CyclicRaw_rangeLayout_raw
import Theorems.Thm_QMAPerfectCompleteness_Main_CyclicRecipe_eval_copies

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
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion
namespace QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic
end QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic

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

/- Inline helpers retained from Solutions.CircuitRecipe. -/
section


/-! Finite circuit-generator recipes. Loops range over unary widths; wire arithmetic is
explicit and preserves the dynamic structure of the paper's polynomial circuit constructions. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CircuitRecipe






namespace Expr







end Expr



namespace Recipe








theorem eval_reverse (p : Recipe) (env : Environment) (ctx : List ℕ)
    (src : List RawEncoding.Instruction) :
    p.reverse.eval env ctx src = (p.eval env ctx src).reverse := by
  induction p generalizing ctx with
  | nil => rfl
  | emit t w => simp [reverse,eval]
  | append a b ia ib => simp [reverse,eval,ia,ib]
  | forUp n b ih => simp [reverse,eval,List.reverse_flatMap,Function.comp_def,ih]
  | forDown n b ih => simp [reverse,eval,List.reverse_flatMap,Function.comp_def,ih]
  | ifLt a b y n iy inn => simp only [reverse,eval]; split_ifs <;> simp [iy,inn]
  | source r w => cases r <;> simp [reverse,eval,List.map_reverse]
  | mapWires w b ih => simp [reverse,eval,ih,List.map_reverse]

end Recipe





end QMAPerfectCompleteness.Main.CircuitRecipe

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

/- Inline helpers retained from Solutions.RecipeGadgets. -/
section


/-! Finite recipes realizing the linear reversible circuit templates. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QMAPerfectCompleteness.Main.CircuitRecipe

namespace Expr

@[simp] theorem eval_plug (e v : Expr) (env : Environment) (ctx : List ℕ) (w : ℕ) :
    (e.plug v).eval env ctx w=e.eval env ctx (v.eval env ctx w) := by
  induction e <;> simp_all [plug,eval]
end Expr

namespace Gadgets
open RawG2 RawEncoding




@[simp] theorem eval_hAppend (p q : Recipe) (env : Environment) (ctx : List ℕ) (src) :
    (p ++ q).eval env ctx src=p.eval env ctx src ++ q.eval env ctx src := rfl
@[simp] theorem eval_add (a b : Expr) (env : Environment) (ctx : List ℕ) (w : ℕ) :
    (a+b).eval env ctx w=a.eval env ctx w+b.eval env ctx w := rfl
@[simp] theorem eval_sub (a b : Expr) (env : Environment) (ctx : List ℕ) (w : ℕ) :
    (a-b).eval env ctx w=a.eval env ctx w-b.eval env ctx w := rfl
@[simp] theorem eval_nat (n : ℕ) (env : Environment) (ctx : List ℕ) (w : ℕ) :
    (OfNat.ofNat n : Expr).eval env ctx w=n := rfl





@[simp] theorem eval_x (a : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (x a).eval env ctx src=[RawG2.x (a.eval env ctx)] := rfl
@[simp] theorem eval_cn (a b : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (cn a b).eval env ctx src=[RawG2.cn (a.eval env ctx) (b.eval env ctx)] := rfl
@[simp] theorem eval_tof (a b c : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (tof a b c).eval env ctx src=[RawG2.tof (a.eval env ctx) (b.eval env ctx) (c.eval env ctx)] := rfl
@[simp] theorem eval_hh (a b : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (hh a b).eval env ctx src=[RawG2.hh (a.eval env ctx) (b.eval env ctx)] := rfl
@[simp] theorem eval_conj (a b c : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (conj a b c).eval env ctx src=[RawG2.compileCommand
      (.conj (a.eval env ctx) (b.eval env ctx) (c.eval env ctx))] := by
  simp only [conj,Recipe.eval,RawG2.compileCommand]
  split_ifs <;> simp_all [tof,cn,Recipe.eval,RawG2.tof,RawG2.cn] <;> omega

/-- Match the syntactic finite index enumeration with the loop counter enumeration. -/
theorem finRange_val (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp













@[simp] theorem eval_useUncompute (a b : Recipe) (env : Environment) (ctx : List ℕ) (src) :
    (useUncompute a b).eval env ctx src=
      RawG2.computeUseUncompute (a.eval env ctx src) (b.eval env ctx src) := by
  simp [useUncompute,RawG2.computeUseUncompute,Recipe.eval_reverse]

/-- The symbolic AND chain is the same literal gate list as the typed clean AND gadget. -/
theorem eval_andCompute (r control flags : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AndLayout (r.eval env ctx))
    (hc : ∀ j, L.controls j=control.eval env ctx j.val)
    (hf : ∀ j, L.flags j=flags.eval env ctx j.val) :
    (andCompute r control flags).eval env ctx src=RawG2.andGates L := by
  simp only [andCompute,eval_hAppend,eval_x,Recipe.eval,eval_tof,
    Expr.eval_plug,Expr.eval_lift,eval_add,eval_nat,Expr.eval]
  unfold RawG2.andGates
  congr 1
  · exact congrArg (fun z=>[RawG2.x z]) (hf 0).symm
  · rw [←finRange_val,List.flatMap_map]
    rw [←List.map_eq_flatMap]
    apply List.map_congr_left
    intro j _
    simp only [hf,hc]
    rfl


theorem eval_multiX (r control flags target : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AndLayout (r.eval env ctx))
    (hc : ∀j,L.controls j=control.eval env ctx j.val)
    (hf : ∀j,L.flags j=flags.eval env ctx j.val) :
    (multiX r control flags target).eval env ctx src=RawG2.multiControlledX L (target.eval env ctx) := by
  simp only [multiX,eval_useUncompute,eval_andCompute r control flags env ctx src L hc hf,
    eval_cn,Expr.eval_plug,RawG2.multiControlledX]
  rw [hf (Fin.last _)]
  rfl

theorem normalizePrefix_flatMap {r : ℕ} (L : RawG2.AndLayout r) (p : Fin r → Bool)
    (t : ℕ) (ht : t≤r) :
    RawG2.normalizePrefix L p t ht=(List.finRange t).flatMap fun j=>
      if p ⟨j.val,Nat.lt_of_lt_of_le j.isLt ht⟩ then []
      else [RawG2.x (L.controls ⟨j.val,Nat.lt_of_lt_of_le j.isLt ht⟩)] := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [RawG2.normalizePrefix,List.finRange_succ_last,List.flatMap_append,
      List.flatMap_map,List.flatMap_singleton]
    rw [ih (by omega)]
    rfl

theorem eval_normalize (r control bit : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AndLayout (r.eval env ctx)) (p : Fin (r.eval env ctx) → Bool)
    (hc : ∀j,L.controls j=control.eval env ctx j.val)
    (hb : ∀j,bit.eval env ctx j.val=if p j then 1 else 0) :
    (normalize r control bit).eval env ctx src=RawG2.normalize L p := by
  simp only [normalize,Recipe.eval,Expr.eval_plug,Expr.eval_lift,Expr.eval]
  rw [←finRange_val,List.flatMap_map]
  unfold RawG2.normalize
  rw [normalizePrefix_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  simp only [List.getElem?_cons_zero,Option.getD_some]
  simp only [hb j]
  cases hp : p j <;> simp [hp,x,Recipe.eval,hc,RawG2.x,Expr.eval]

theorem eval_patternX (r control flags bit target : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AndLayout (r.eval env ctx)) (p : Fin (r.eval env ctx) → Bool)
    (hc : ∀j,L.controls j=control.eval env ctx j.val)
    (hf : ∀j,L.flags j=flags.eval env ctx j.val)
    (hb : ∀j,bit.eval env ctx j.val=if p j then 1 else 0) :
    (patternX r control flags bit target).eval env ctx src=RawG2.patternControlledX L p (target.eval env ctx) := by
  simp only [patternX,eval_useUncompute,eval_normalize r control bit env ctx src L p hc hb,
    eval_multiX r control flags target env ctx src L hc hf,RawG2.patternControlledX]







@[simp] theorem eval_borrowStep (a b carry next temp : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (borrowStep a b carry next temp).eval env ctx src=
      RawG2.compile (RawG2.borrowCommands ![a.eval env ctx,b.eval env ctx,carry.eval env ctx,
        next.eval env ctx,temp.eval env ctx]) := by
  simp only [borrowStep,eval_hAppend,eval_cn,eval_x,eval_conj]
  rfl

theorem borrowPrefix_flatMap {r : ℕ} (L : RawG2.BorrowLayout r) (t : ℕ) (ht : t≤r) :
    RawG2.borrowPrefix L t ht=(List.finRange t).flatMap fun j=>
      RawG2.borrowCommands ![L.left ⟨j.val,Nat.lt_of_lt_of_le j.isLt ht⟩,
        L.right ⟨j.val,Nat.lt_of_lt_of_le j.isLt ht⟩,
        L.carry ⟨j.val,by have := j.isLt; omega⟩,L.carry ⟨j.val+1,by have := j.isLt; omega⟩,L.temp] := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [RawG2.borrowPrefix,List.finRange_succ_last,List.flatMap_append,
      List.flatMap_map,List.flatMap_singleton]
    rw [ih (by omega)]
    rfl

theorem eval_borrowCompute (r a b carry temp : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.BorrowLayout (r.eval env ctx))
    (ha : ∀j,L.left j=a.eval env ctx j.val)
    (hb : ∀j,L.right j=b.eval env ctx j.val)
    (hc : ∀j,L.carry j=carry.eval env ctx j.val)
    (hp : L.temp=temp.eval env ctx) :
    (borrowCompute r a b carry temp).eval env ctx src=
      RawG2.compile (RawG2.borrowPrefix L (r.eval env ctx) le_rfl) := by
  simp only [borrowCompute,Recipe.eval,eval_borrowStep,Expr.eval_plug,Expr.eval_lift,
    eval_add,eval_nat,Expr.eval]
  rw [←finRange_val,List.flatMap_map,borrowPrefix_flatMap]
  simp only [RawG2.compile,List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  simp only [ha,hb,hc,hp]
  rfl

theorem eval_comparator (r a b carry temp target : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.BorrowLayout (r.eval env ctx))
    (ha : ∀j,L.left j=a.eval env ctx j.val)
    (hb : ∀j,L.right j=b.eval env ctx j.val)
    (hc : ∀j,L.carry j=carry.eval env ctx j.val)
    (hp : L.temp=temp.eval env ctx) :
    (comparator r a b carry temp target).eval env ctx src=RawG2.comparator L (target.eval env ctx) := by
  simp only [comparator,eval_useUncompute,eval_borrowCompute r a b carry temp env ctx src L ha hb hc hp,
    eval_cn,Expr.eval_plug,RawG2.comparator]
  rw [hc (Fin.last _)]
  rfl



theorem eval_equality (r a b carry temp target : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.BorrowLayout (r.eval env ctx))
    (ha : ∀j,L.left j=a.eval env ctx j.val)
    (hb : ∀j,L.right j=b.eval env ctx j.val)
    (hc : ∀j,L.carry j=carry.eval env ctx j.val)
    (hp : L.temp=temp.eval env ctx) :
    (equality r a b carry temp target).eval env ctx src=RawG2.equality L (target.eval env ctx) := by
  simp only [equality,eval_hAppend,eval_x,RawG2.equality]
  rw [eval_comparator r a b carry temp target env ctx src L ha hb hc hp,
    eval_comparator r b a carry temp target env ctx src (RawG2.swapBorrow L) hb ha hc hp]










@[simp] theorem eval_carryStep (a b carry next temp : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (carryStep a b carry next temp).eval env ctx src=
      RawG2.compile (RawG2.carryCommands ![a.eval env ctx,b.eval env ctx,carry.eval env ctx,
        next.eval env ctx,temp.eval env ctx]) := by
  simp only [carryStep,eval_hAppend,eval_cn,eval_conj]
  rfl

theorem carryPrefix_flatMap {r : ℕ} (L : RawG2.AdditionLayout r) (t : ℕ) (ht : t≤r) :
    RawG2.carryPrefix L t ht=(List.finRange t).flatMap fun j=>
      RawG2.carryCommands ![L.left ⟨j.val,Nat.lt_of_lt_of_le j.isLt ht⟩,
        L.right ⟨j.val,Nat.lt_of_lt_of_le j.isLt ht⟩,
        L.carry ⟨j.val,by have := j.isLt; omega⟩,L.carry ⟨j.val+1,by have := j.isLt; omega⟩,L.temp] := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [RawG2.carryPrefix,List.finRange_succ_last,List.flatMap_append,
      List.flatMap_map,List.flatMap_singleton]
    rw [ih (by omega)]
    rfl

theorem eval_carryCompute (r a b carry temp : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AdditionLayout (r.eval env ctx))
    (ha : ∀j,L.left j=a.eval env ctx j.val)
    (hb : ∀j,L.right j=b.eval env ctx j.val)
    (hc : ∀j,L.carry j=carry.eval env ctx j.val)
    (hp : L.temp=temp.eval env ctx) :
    (carryCompute r a b carry temp).eval env ctx src=
      RawG2.compile (RawG2.carryPrefix L (r.eval env ctx) le_rfl) := by
  simp only [carryCompute,Recipe.eval,eval_carryStep,Expr.eval_plug,Expr.eval_lift,
    eval_add,eval_nat,Expr.eval]
  rw [←finRange_val,List.flatMap_map,carryPrefix_flatMap]
  simp only [RawG2.compile,List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  simp only [ha,hb,hc,hp]
  rfl

theorem eval_sumCompute (r a b carry output : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AdditionLayout (r.eval env ctx))
    (ha : ∀j,L.left j=a.eval env ctx j.val)
    (hb : ∀j,L.right j=b.eval env ctx j.val)
    (hc : ∀j,L.carry j=carry.eval env ctx j.val)
    (ho : ∀j,L.output j=output.eval env ctx j.val) :
    (sumCompute r a b carry output).eval env ctx src=
      RawG2.compile ((List.finRange (r.eval env ctx)).flatMap (RawG2.sumStep L)) := by
  simp only [sumCompute,Recipe.eval,eval_hAppend,eval_cn,Expr.eval_plug,Expr.eval_lift,Expr.eval]
  rw [←finRange_val,List.flatMap_map]
  simp only [RawG2.compile,List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  simp only [RawG2.sumStep,ha,hb,hc,ho]
  rfl

theorem eval_addition (r a b carry output temp : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AdditionLayout (r.eval env ctx))
    (ha : ∀j,L.left j=a.eval env ctx j.val)
    (hb : ∀j,L.right j=b.eval env ctx j.val)
    (hc : ∀j,L.carry j=carry.eval env ctx j.val)
    (ho : ∀j,L.output j=output.eval env ctx j.val)
    (hp : L.temp=temp.eval env ctx) :
    (addition r a b carry output temp).eval env ctx src=RawG2.addition L := by
  simp only [addition,eval_useUncompute,
    eval_carryCompute r a b carry temp env ctx src L ha hb hc hp,
    eval_sumCompute r a b carry output env ctx src L ha hb hc ho,
    RawG2.addition,RawG2.additionCommands,RawG2.compile,List.map_append,List.map_reverse,
    RawG2.computeUseUncompute]










theorem incrementPrefix_flatMap {r : ℕ} (L : RawG2.AndLayout (r+1)) (t : ℕ) (ht : t≤r) :
    RawG2.incrementPrefix L t ht=((List.finRange t).reverse).flatMap fun j=>
      RawG2.incrementStep L j.val (Nat.lt_of_lt_of_le j.isLt ht) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [RawG2.incrementPrefix,List.finRange_succ_last,List.reverse_append,
      List.reverse_singleton,List.flatMap_append,List.flatMap_singleton,←List.map_reverse,List.flatMap_map]
    rw [ih (by omega)]
    rfl

theorem eval_increment (r control flags : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AndLayout (r.eval env ctx+1))
    (hc : ∀j,L.controls j=control.eval env ctx j.val)
    (hf : ∀j,L.flags j=flags.eval env ctx j.val) :
    (increment r control flags).eval env ctx src=RawG2.increment L := by
  simp only [increment,Recipe.eval]
  rw [←finRange_val,←List.map_reverse,List.flatMap_map]
  unfold RawG2.increment
  rw [incrementPrefix_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  unfold RawG2.incrementStep
  convert eval_multiX (.bound 0+1) control.lift flags.lift
    (control.lift.plug (.bound 0+1)) env (j.val::ctx) src
    (RawG2.prefixLayout L (j.val+1) (by have := j.isLt; omega))
    (fun i=>by simp [RawG2.prefixLayout,hc]) (fun i=>by simp [RawG2.prefixLayout,hf]) using 1
  · simp [hc,Expr.eval]



theorem eval_pairedH (r wire : Expr) (env : Environment) (ctx : List ℕ) (src)
    (e : Fin (r.eval env ctx) → ℕ) (he : ∀j,e j=wire.eval env ctx j.val) :
    (pairedH r wire).eval env ctx src=RawG2.pairedHadamards e := by
  simp only [pairedH,Recipe.eval,Expr.eval,eval_hh,Expr.eval_plug,Expr.eval_lift,eval_add,
    eval_nat]
  rw [←finRange_val,List.flatMap_map,←List.map_eq_flatMap]
  unfold RawG2.pairedHadamards
  apply List.map_congr_left
  intro j _
  simp only [he,eval_nat]
  rfl


end Gadgets
end QMAPerfectCompleteness.Main.CircuitRecipe

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

/- Inline helpers retained from Solutions.CyclicRawCorrectness. -/
section


/-! Literal raw-code correspondence for the coherent certificate compiler. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace QMAPerfectCompleteness.Main.CyclicRaw
open RawEncoding RawG2 CertificateMasterLayout


@[simp] theorem params_eq_source (V : Verifier gatesG2) : params V=sourceMeta V := ofRaw_erase V

@[ext] theorem and_ext {r : ℕ} (L M : RawG2.AndLayout r)
    (hc : ∀j,L.controls j=M.controls j) (hf : ∀j,L.flags j=M.flags j) : L=M := by
  cases L; cases M
  simp only [AndLayout.mk.injEq]
  exact ⟨funext hc,funext hf⟩

@[ext] theorem borrow_ext {r : ℕ} (L M : RawG2.BorrowLayout r)
    (ha : ∀j,L.left j=M.left j) (hb : ∀j,L.right j=M.right j)
    (hc : ∀j,L.carry j=M.carry j) (hp : L.temp=M.temp) : L=M := by
  cases L; cases M
  simp only [BorrowLayout.mk.injEq]
  exact ⟨funext ha,funext hb,funext hc,hp⟩

@[simp] theorem source_word (V : Verifier gatesG2) (d : Fin 6) (j : Fin (r V)) :
    (prepWord V d j).val=(sourceMeta V).word d.val j.val := by
  simpa only [params_eq_source] using word_meta V d j
@[simp] theorem source_certificate (V : Verifier gatesG2) (s : Fin 2) (j : Fin (k V)) :
    (certificate V s j).val=(sourceMeta V).certificate s.val j.val := by
  simpa only [params_eq_source] using certificate_meta V s j

@[simp] theorem thresholdLayout_raw (V : Verifier gatesG2) :
    eraseThreshold (CertificatePreparation.thresholdLayout V)=(sourceMeta V).thresholds := by
  change ThresholdLayout.mk _ _ _ _ = ThresholdLayout.mk _ _ _ _
  congr 1
  · funext d j
    exact source_certificate V d j
  · funext d j
    exact source_word V d j

@[simp] theorem prepGates_raw (V : Verifier gatesG2) :
    (CertificatePreparation.prepGates V).map eraseInstr=(sourceMeta V).prepGates := by
  rw [CertificatePreparation.prepGates,erase_threshold,thresholdLayout_raw]
  rfl

@[simp] theorem erase_wires_comparator {n r : ℕ} (W : DynamicBlockCompiler.RangeWires n r) (d : Fin 3) :
    eraseBorrow (W.comparator d)=
      ⟨fun j=>(W.index j).val,fun j=>(W.thresholds d j).val,
        fun j=>(W.scratch (Fin.castAdd 1 j)).val,(W.scratch (Fin.last (r+1))).val⟩ := by
  apply borrow_ext
  · intro j; exact congrArg Fin.val (W.comparator_left d j)
  · intro j; exact congrArg Fin.val (W.comparator_right d j)
  · intro j; exact congrArg Fin.val (W.comparator_carry d j)
  · exact congrArg Fin.val (W.comparator_temp d)



@[simp] theorem rangeGates_raw (V : Verifier gatesG2) :
    (CertificateRangeCircuit.gates V).map eraseInstr=(sourceMeta V).rangeGates := by
  rw [CertificateRangeCircuit.gates,erase_range,rangeLayout_raw]
  rfl

@[simp] theorem validityLayout_raw (V : Verifier gatesG2) :
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

@[simp] theorem validGates_raw (V : Verifier gatesG2) :
    (CertificateValidityCircuit.gates V).map eraseInstr=(sourceMeta V).validGates := by
  unfold CertificateValidityCircuit.gates CertificateValidityCircuit.program
  rw [erase_validity,validityLayout_raw]
  rfl

@[simp] theorem prefixGates_raw (V : Verifier gatesG2) :
    (CertificatePreparation.prefixGates V).map eraseInstr=(sourceMeta V).prefixGates := by
  simp only [CertificatePreparation.prefixGates,List.map_append,prepGates_raw,validGates_raw]
  rfl



@[simp] theorem closingGates_raw (V : Verifier gatesG2) :
    (CertificateClosingCircuit.gates V).map eraseInstr=
      RawG2.closing (sourceMeta V).historyLayout ((sourceMeta V).tag 4) (sourceMeta V).flag := by
  rw [CertificateClosingCircuit.gates,erase_closing]
  change RawG2.closing (eraseHistory (CertificateMasterLayout.historyLayout V)) _ _ = _
  rw [historyLayout_raw]
  rfl

@[simp] theorem place_id (gs : List RawEncoding.Instruction) : RawG2.place id gs=gs := by
  simp [RawG2.place]

@[simp] theorem hadamards_raw (V : Verifier gatesG2) :
    (CertificateHadamardCoordinates.gates V (work V)).map eraseInstr=(sourceMeta V).indexH := by
  unfold CertificateHadamardCoordinates.gates IndexHadamards.pairedHadamards
    Meta.indexH RawG2.pairedHadamards
  simp only [List.map_map]
  apply List.map_congr_left
  intro j _
  rfl

@[simp] theorem forward_raw (V : Verifier gatesG2) :
    (CertificateVerifierCoordinates.forward V (work V)).map eraseInstr=
      RawG2.place (sourceMeta V).verifier (eraseVerifier V).gates := by
  unfold CertificateVerifierCoordinates.forward BlockCircuit.forwardGates
  rw [erase_mapGates _ id (fun _=>rfl),place_id]
  exact erase_mapGates _ (sourceMeta V).verifier (fun _=>rfl) V.gates

@[simp] theorem backward_raw (V : Verifier gatesG2) :
    (CertificateVerifierCoordinates.backward V (work V)).map eraseInstr=
      RawG2.place (sourceMeta V).verifier (eraseVerifier V).gates.reverse := by
  unfold CertificateVerifierCoordinates.backward BlockCircuit.backwardGates
  rw [erase_mapGates _ id (fun _=>rfl),place_id]
  rw [List.map_reverse,BlockCircuit.forwardGates,erase_mapGates _ (sourceMeta V).verifier (fun _=>rfl)]
  simp only [RawG2.place,List.map_reverse]
  rfl

@[simp] theorem mid_raw (V : Verifier gatesG2) :
    (CertificateOldPrograms.midProgram V).gates.map eraseInstr=(sourceMeta V).mid := by
  unfold CertificateOldPrograms.midProgram BlockCompiler.CleanProgram.mapWires
  rw [erase_mapGates _ id (fun _=>rfl),place_id,BlockCompiler.Layout.midProgram_gates]
  simp only [BlockCompiler.Layout.mid,List.map_append,List.map_reverse,
    BlockCompiler.Layout.clockBelowGates,erase_compareNatGates,erase_tripleControlledX]
  rfl

@[simp] theorem increment_raw (V : Verifier gatesG2) :
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

@[simp] theorem identity_raw (V : Verifier gatesG2) :
    (CertificateOldPrograms.identityFlagProgram V).gates.map eraseInstr=
      [RawG2.cn ((sourceMeta V).tag 0) (sourceMeta V).flag] := by
  unfold CertificateOldPrograms.identityFlagProgram BlockCompiler.CleanProgram.mapWires
  rw [erase_mapGates _ id (fun _=>rfl),place_id]
  rfl

@[simp] theorem phase_raw (V : Verifier gatesG2) :
    (CertificateOldPrograms.phaseGates V).map eraseInstr=
      RawG2.phase ((sourceMeta V).tag 5) ((sourceMeta V).tag 9) := by
  unfold CertificateOldPrograms.phaseGates
  rw [erase_mapGates _ id (fun _=>rfl),place_id,erase_phase]
  rfl

@[simp] theorem post_raw (V : Verifier gatesG2) :
    (CertificateBlockCorrectness.postGates V).map eraseInstr=(sourceMeta V).post := by
  simp only [CertificateBlockCorrectness.postGates,List.map_append,closingGates_raw,
    identity_raw,increment_raw,phase_raw,Meta.post]

@[simp] theorem readoutLayout_raw (V : Verifier gatesG2) :
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

@[simp] theorem readoutGates_raw (V : Verifier gatesG2) :
    (readoutGates V).map eraseInstr=RawG2.readout (sourceMeta V).readoutLayout := by
  rw [readoutGates,erase_readout,readoutLayout_raw]


@[simp] theorem block_raw (V : Verifier gatesG2) :
    (CertificateBlockCorrectness.gates V).map eraseInstr=(sourceMeta V).block (eraseVerifier V).gates := by
  simp only [CertificateBlockCorrectness.gates,CertificateBlockCorrectness.selectGates,
    List.map_append,List.map_reverse,hadamards_raw,rangeGates_raw,forward_raw,backward_raw,
    mid_raw,post_raw,Meta.block]

@[simp] theorem gates_raw (V : Verifier gatesG2) :
    (CyclicVerifier.gates V).map eraseInstr=(sourceMeta V).gates (eraseVerifier V).gates := by
  simp only [CyclicVerifier.gates,List.map_append,prefixGates_raw,block_raw,readoutGates_raw,
    Meta.gates,CertificateEtaTransport.gates,List.map_cons,List.map_nil,erase_x]
  rfl

theorem circuit_ext (A B : RawEncoding.Circuit)
    (hm : A.proofQubits=B.proofQubits) (ha : A.ancillaQubits=B.ancillaQubits)
    (ho : A.output=B.output) (hg : A.gates=B.gates) : A=B := by
  cases A; cases B
  simp only [RawEncoding.Circuit.mk.injEq]
  exact ⟨hm,ha,ho,hg⟩

/-- The executable raw compiler emits precisely the already-verified coherent verifier. -/
theorem compileRaw_erase (V : Verifier gatesG2) :
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







end QMAPerfectCompleteness.Main.CyclicRaw

end

/- Inline helpers retained from Solutions.CyclicRecipeCorrectness. -/
section


/-! Exact realization of the coherent verifier by a finite circuit-generator recipe. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace QMAPerfectCompleteness.Main.CyclicRecipe
open CircuitRecipe CircuitRecipe.Gadgets RawEncoding RawG2



@[simp] theorem eval_out (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    out.eval P.env ctx w=P.out := rfl

@[simp] theorem eval_k (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    k.eval P.env ctx w=P.k := rfl







@[simp] theorem eval_proof (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    proof.eval P.env ctx w=P.proof := rfl
@[simp] theorem eval_ancilla (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    ancilla.eval P.env ctx w=P.ancilla := rfl
@[simp] theorem eval_clock (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    clock.eval P.env ctx w=P.clock w := rfl
@[simp] theorem eval_verifier (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    verifier.eval P.env ctx w=P.verifier w := rfl

@[simp] theorem eval_carry (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    carry.eval P.env ctx w=P.carry w := rfl
@[simp] theorem eval_pad (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    pad.eval P.env ctx w=P.pad w := rfl


@[simp] theorem eval_flag (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    flag.eval P.env ctx w=P.flag := rfl
@[simp] theorem eval_temp (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    temp.eval P.env ctx w=P.temp := rfl
@[simp] theorem eval_readoutZero (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    readoutZero.eval P.env ctx w=P.readoutZero := rfl
@[simp] theorem eval_readoutOutput (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    readoutOutput.eval P.env ctx w=P.readoutOutput := rfl
@[simp] theorem eval_tag (P : CyclicRaw.Meta) (j : ℕ) (ctx : List ℕ) (w : ℕ) :
    (tag j).eval P.env ctx w=P.tag j := rfl
@[simp] theorem eval_validTag (P : CyclicRaw.Meta) (j : ℕ) (ctx : List ℕ) (w : ℕ) :
    (validTag j).eval P.env ctx w=P.validity j := rfl
@[simp] theorem eval_word (P : CyclicRaw.Meta) (d : ℕ) (ctx : List ℕ) (w : ℕ) :
    (word d).eval P.env ctx w=P.word d w := rfl


@[simp] theorem eval_paddedIndex (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    paddedIndex.eval P.env ctx w=P.paddedIndex w := by
  simp only [paddedIndex,Expr.eval,eval_k,Expr.eval_plug,eval_pad,eval_sub]
  rfl

@[simp] theorem eval_incControl (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    incControl.eval P.env ctx w=if w=0 then P.tag 5 else P.clock (w-1) := by
  simp only [incControl,Expr.eval,Expr.eval_plug,eval_tag,eval_clock,eval_sub,eval_nat]
  split_ifs <;> omega
@[simp] theorem eval_permute (P : CyclicRaw.Meta) (ctx : List ℕ) (w : ℕ) :
    permute.eval P.env ctx w=P.permute w := rfl

theorem eval_andNot (a b c : Expr) (env : Environment) (ctx : List ℕ) (src) :
    (andNot a b c).eval env ctx src=RawG2.andNot (a.eval env ctx) (b.eval env ctx) (c.eval env ctx) := by
  simp only [andNot,eval_hAppend,eval_x,eval_conj]
  rfl

@[simp] theorem eval_range (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    range.eval P.env ctx src=P.rangeGates := by
  have hc (d t : ℕ) :
      (Gadgets.comparator r paddedIndex (word d) carry temp (tag t)).eval P.env ctx src=
        RawG2.comparator (P.arithmeticBorrow P.paddedIndex (P.word d)) (P.tag t) := by
    apply eval_comparator _ _ _ _ _ _ P.env ctx src
      <;> intros <;> simp [CyclicRaw.Meta.arithmeticBorrow]
  simp only [range,eval_hAppend,hc,eval_andNot,eval_tag]
  rfl

@[simp] theorem eval_proofEquality (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    proofEquality.eval P.env ctx src=RawG2.equality P.historyLayout.equality (P.tag 8) := by
  apply eval_equality _ _ _ _ _ _ P.env ctx src
    <;> intros <;> rfl

@[simp] theorem eval_lastClock (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    lastClock.eval P.env ctx src=RawG2.patternControlledX P.clockAnd (fun _=>true) (P.tag 6) := by
  apply eval_patternX _ _ _ _ _ P.env ctx src
    <;> intros <;> rfl

@[simp] theorem eval_history (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    history.eval P.env ctx src=RawG2.history P.historyLayout := by
  simp only [history,eval_hAppend,eval_proofEquality,eval_lastClock,eval_tof,eval_tag,Recipe.eval_reverse]
  rfl

@[simp] theorem eval_closing (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    closing.eval P.env ctx src=RawG2.closing P.historyLayout (P.tag 4) P.flag := by
  simp only [closing,eval_useUncompute,eval_history,eval_tof,eval_tag,eval_flag]
  rfl

@[simp] theorem eval_indexH (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    indexH.eval P.env ctx src=P.indexH := by
  apply eval_pairedH _ _ P.env ctx src
  intros
  rfl

@[simp] theorem eval_increment (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    (Gadgets.increment c incControl scratch).eval P.env ctx src=RawG2.increment P.incrementLayout := by
  apply Gadgets.eval_increment _ _ _ P.env ctx src
  · intro j; exact (eval_incControl P ctx j.val).symm
  · intro j; rfl

@[simp] theorem eval_post (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    post.eval P.env ctx src=P.post := by
  simp only [post,eval_hAppend,eval_cn,eval_tag,eval_flag,eval_closing,eval_increment,eval_hh,eval_x]
  simp [CyclicRaw.Meta.post,RawG2.phase,List.append_assoc]

@[simp] theorem eval_zeroTest (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    zeroTest.eval P.env ctx src=RawG2.patternControlledX P.readoutLayout.zeros (fun _=>false) P.readoutZero := by
  apply eval_patternX _ _ _ _ _ P.env ctx src
    <;> intros <;> rfl

@[simp] theorem eval_readout (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    readout.eval P.env ctx src=RawG2.readout P.readoutLayout := by
  simp only [readout,eval_useUncompute,eval_zeroTest,eval_hAppend,eval_x,eval_conj,
    eval_readoutZero,eval_readoutOutput,eval_validTag]
  rfl

end QMAPerfectCompleteness.Main.CyclicRecipe

end

/- Inline helpers retained from Solutions.CyclicRecipePreparation. -/
section


/-! The finite arithmetic prefix recipe matches the proved clean adder circuits. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace QMAPerfectCompleteness.Main.CyclicRecipe
open CircuitRecipe CircuitRecipe.Gadgets RawEncoding RawG2





@[simp] theorem eval_three (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    (Gadgets.addition r (word 0) (word 1) carry (word 4) temp).eval P.env ctx src=
      RawG2.addition (RawG2.threeLayout P.thresholds) := by
  apply eval_addition _ _ _ _ _ _ P.env ctx src
    <;> intros <;> rfl

@[simp] theorem eval_upper (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    (Gadgets.addition r (word 4) (word 2) carry (word 5) temp).eval P.env ctx src=
      RawG2.addition (RawG2.upperLayout P.thresholds) := by
  apply eval_addition _ _ _ _ _ _ P.env ctx src
    <;> intros <;> rfl

@[simp] theorem eval_threshold (P : CyclicRaw.Meta) (ctx : List ℕ) (src) :
    threshold.eval P.env ctx src=P.prepGates := by
  simp only [threshold,eval_hAppend,eval_copies,eval_three,eval_upper]
  simp only [CyclicRaw.Meta.prepGates,RawG2.threshold,RawG2.thresholdCommands,
    RawG2.compile,RawG2.addition,List.map_append]

end QMAPerfectCompleteness.Main.CyclicRecipe

end

/- Inline helpers retained from Solutions.CyclicRecipeValidity. -/
section


/-! Sparse threshold bits realize validity without exponential unary constants. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace QMAPerfectCompleteness.Main.CyclicRecipe
open CircuitRecipe CircuitRecipe.Gadgets RawEncoding RawG2

theorem eval_bitAt_pattern (pos : Expr) (env : Environment) (ctx : List ℕ) (n : ℕ)
    (hn : ∀w,pos.eval env ctx w=n) (j : ℕ) :
    (bitAt pos).eval env ctx j=if (2^n).testBit j then 1 else 0 := by
  simp only [bitAt,Expr.eval,hn,Nat.testBit_two_pow,decide_eq_true_eq]
  split_ifs <;> omega

lemma testBit_pow_add_one (n j : ℕ) (hn : 0<n) :
    (2^n+1).testBit j=decide (j=0 ∨ j=n) := by
  have h := Nat.testBit_two_pow_mul_add 1 (Nat.one_lt_two_pow (by omega : n≠0)) j
  simp only [Nat.mul_one] at h
  rw [h]
  have h1 (t : ℕ) : (1 : ℕ).testBit t=decide (0=t) := by
    exact Nat.testBit_two_pow (n:=0) (m:=t)
  simp only [h1]
  by_cases hj : j<n
  · rw [if_pos hj]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  · rw [if_neg hj]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega

theorem eval_upperBits (P : CyclicRaw.Meta) (ctx : List ℕ) (hk : 3≤P.k) (j : ℕ) :
    upperBits.eval P.env ctx j=if (2^(P.k-2)+1).testBit j then 1 else 0 := by
  rw [testBit_pow_add_one _ _ (by omega)]
  simp only [upperBits,bitAt,Expr.eval,eval_sub,eval_k,eval_nat,CyclicRaw.Meta.env,decide_eq_true_eq]
  split_ifs <;> omega

lemma one_lt_width (P : CyclicRaw.Meta) : 1<2^P.r := by
  exact Nat.one_lt_two_pow (by dsimp [CyclicRaw.Meta.r]; omega)
lemma low_lt_width (P : CyclicRaw.Meta) : 2^(P.k-3)<2^P.r := by
  exact Nat.pow_lt_pow_right (by decide : 1<2) (by dsimp [CyclicRaw.Meta.r]; omega)
lemma upper_lt_width (P : CyclicRaw.Meta) : 2^(P.k-2)+1<2^P.r := by
  have h := Nat.pow_le_pow_right (by decide : 0<2) (show P.k-2+2≤P.r by dsimp [CyclicRaw.Meta.r]; omega)
  have h2 : 0<2^(P.k-2) := Nat.two_pow_pos _
  rw [Nat.pow_succ,Nat.pow_succ] at h
  omega

/-- A generic constant-comparison recipe with a supplied compact threshold bit formula. -/
theorem compare_constant (P : CyclicRaw.Meta) (ctx : List ℕ) (src) (d t N : ℕ) (bits : Expr)
    (hN : N<2^P.r) (hb : ∀j : Fin P.r,bits.eval P.env ctx j.val=if N.testBit j.val then 1 else 0) :
    (compareBits r (word d) carry bits (validTag t)).eval P.env ctx src=
      RawG2.compareNatGates (r:=P.r)
        ⟨fun j=>P.word d j.val,fun j=>P.carry j.val⟩ N (P.validity t) := by
  unfold RawG2.compareNatGates
  rw [if_pos hN]
  apply eval_compareBits _ _ _ _ _ P.env ctx src
  · intro j; rfl
  · intro j; rfl
  · exact hb

@[simp] theorem eval_criteria (P : CyclicRaw.Meta) (ctx : List ℕ) (src) (hk : 3≤P.k) :
    criteria.eval P.env ctx src=RawG2.criteria P.validityLayout := by
  have h1 d t := compare_constant P ctx src d t 1 (bitAt 0) (one_lt_width P)
    (fun j=>by simpa only [Nat.pow_zero] using eval_bitAt_pattern 0 P.env ctx 0 (fun _=>rfl) j.val)
  have h2 := compare_constant P ctx src 0 2 (2^(P.k-3)) (bitAt (k-3)) (low_lt_width P)
    (fun j=>eval_bitAt_pattern (k-3) P.env ctx (P.k-3) (fun _=>rfl) j.val)
  have h3 := compare_constant P ctx src 0 3 (2^(P.k-2)+1) upperBits (upper_lt_width P)
    (fun j=>eval_upperBits P ctx hk j.val)
  have hv : (Gadgets.comparator r (word 0) (word 3) carry temp (validTag 4)).eval P.env ctx src=
      RawG2.comparator P.validityLayout.comparison (P.validity 4) := by
    apply eval_comparator _ _ _ _ _ _ P.env ctx src <;> intros <;> rfl
  simp only [criteria,eval_hAppend,h1,h2,h3,hv,eval_x,eval_validTag]
  rfl

@[simp] theorem eval_validity (P : CyclicRaw.Meta) (ctx : List ℕ) (src) (hk : 3≤P.k) :
    validity.eval P.env ctx src=P.validGates := by
  unfold validity CyclicRaw.Meta.validGates RawG2.validity
  rw [eval_hAppend,eval_criteria P ctx src hk]
  congr 1
  apply eval_multiX _ _ _ _ P.env ctx src
  · intro j; rfl
  · intro j
    change P.carry (min j.val (P.k+2))=P.carry j.val
    have hj : j.val<6 := j.isLt
    rw [min_eq_left (by omega)]

@[simp] theorem eval_clockBelow (P : CyclicRaw.Meta) (ctx : List ℕ) (src)
    (hell : P.ell=2^P.c-1) : clockBelow.eval P.env ctx src=
      RawG2.compareNatGates P.clockAnd P.ell (P.tag 6) := by
  unfold clockBelow RawG2.compareNatGates
  have hlt : P.ell<2^P.c := by rw [hell]; have := Nat.two_pow_pos P.c; omega
  rw [if_pos hlt]
  apply eval_compareBits _ _ _ _ _ P.env ctx src
  · intro j; rfl
  · intro j; rfl
  · intro j
    rw [hell,Nat.testBit_two_pow_sub_one]
    simp [j.isLt,Expr.eval]

@[simp] theorem eval_mid (P : CyclicRaw.Meta) (ctx : List ℕ) (src) (hell : P.ell=2^P.c-1) :
    mid.eval P.env ctx src=P.mid := by
  simp only [mid,eval_useUncompute,eval_clockBelow P ctx src hell,tripleFlag,eval_hAppend,
    eval_tof,eval_tag,eval_flag,Expr.eval_plug,eval_verifier,eval_out]
  rfl

end QMAPerfectCompleteness.Main.CyclicRecipe

end

/- Inline helpers retained from Solutions.CyclicRecipeRealization. -/
section


/-! Final executable finite-recipe realization of the paper's coherent certificate verifier. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace QMAPerfectCompleteness.Main.CyclicRecipe
open CircuitRecipe CircuitRecipe.Gadgets RawEncoding RawG2

@[simp] theorem eval_preparation (P : CyclicRaw.Meta) (ctx : List ℕ) (src) (hk : 3≤P.k) :
    preparation.eval P.env ctx src=P.prefixGates := by
  simp only [preparation,eval_hAppend,eval_threshold,eval_validity P ctx src hk]
  rfl

@[simp] theorem eval_source (P : CyclicRaw.Meta) (ctx : List ℕ) (src) (rev : Bool) :
    (Recipe.source rev verifier).eval P.env ctx src=
      RawG2.place P.verifier (if rev then src.reverse else src) := by
  simp only [Recipe.eval,eval_verifier]
  rfl

@[simp] theorem eval_block (P : CyclicRaw.Meta) (ctx : List ℕ) (src)
    (hell : P.ell=2^P.c-1) : block.eval P.env ctx src=P.block src := by
  simp only [block,eval_hAppend,eval_indexH,eval_range,eval_source,eval_mid P ctx src hell,
    eval_post,Recipe.eval_reverse,Bool.false_eq_true,if_false,if_true]
  rfl

@[simp] theorem eval_physical (P : CyclicRaw.Meta) (ctx : List ℕ) (src)
    (hk : 3≤P.k) (hell : P.ell=2^P.c-1) : physical.eval P.env ctx src=P.gates src := by
  simp only [physical,eval_hAppend,eval_x,eval_flag,eval_preparation P ctx src hk,
    eval_block P ctx src hell,eval_readout]
  rfl

/-- A fixed finite recipe evaluates to the exact raw circuit, using only width-bounded loops. -/
theorem program_eval (P : CyclicRaw.Meta) (src : List RawEncoding.Instruction)
    (hk : 3≤P.k) (hell : P.ell=2^P.c-1) : program.eval P.env src=P.compile src := by
  unfold program CircuitRecipe.Circuit.eval
  simp only [eval_proof,eval_ancilla,Expr.eval_plug,eval_permute,eval_readoutOutput,
    Recipe.eval,eval_physical P [] src hk hell,eval_permute]
  rfl

/-- The finite recipe emits precisely the verified typed cyclic verifier on every valid code. -/
theorem compileRaw_erase (V : Verifier gatesG2) :
    compileRaw (eraseVerifier V)=eraseVerifier (CyclicVerifier.compileVerifier V) := by
  have hk : 3≤(CyclicRaw.params V).k := by
    rw [CyclicRaw.k_meta]
    dsimp only [indexQubits]
    omega
  have hell : (CyclicRaw.params V).ell=2^(CyclicRaw.params V).c-1 := by
    rw [CyclicRaw.params_eq_source]
    rfl
  unfold compileRaw
  rw [program_eval _ _ hk hell]
  exact CyclicRaw.compileRaw_erase V



@[simp] theorem executableCompile_encode (V : Verifier gatesG2) :
    executableCompile V.encode=(CyclicVerifier.compileVerifier V).encode := by
  simp only [executableCompile,RawEncoding.decodeCircuit_encode _ RawEncoding.g2Table_correct,
    compileRaw_erase,RawEncoding.eraseVerifier_encode]

end QMAPerfectCompleteness.Main.CyclicRecipe

end

/- Inline helpers retained from Solutions.UnaryNextPowerCorrectness. -/
section


/-! Correctness and polynomial execution time of the finite unary ceiling-log2 machine. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.UnaryNextPowerTM
open QAlgorithms.Complexity (Str encNat)































@[simp] lemma compile_encode (a : ℕ) (tail : Str) : compile (encNat a++tail) = outputCode a tail := by
  simp [compile]

/-- This continuation needs a timed witness only on the generator's unary-prefixed outputs. -/
theorem polyTime_on_unary_prefix {f : Str → Str}
    (hf : QAlgorithms.Complexity.PolyTimeComputable f)
    (a : Str → ℕ) (payload : Str → Str) (hcode : ∀ s, f s=encNat (a s)++payload s) :
    QAlgorithms.Complexity.PolyTimeComputable (fun s => outputCode (a s) (payload s)) := by
  obtain ⟨hf⟩ := hf
  have h := BinaryComposition.computableContinuation (g := compile) hf machine
    (Equiv.refl Bool) (Equiv.refl Bool) timePolynomial (fun s => by
      simp only [Equiv.refl,List.map_id_fun,id_eq]
      rw [hcode s,compile_encode]
      exact outputs (a s) (payload s))
  have he : compile ∘ f = fun s => outputCode (a s) (payload s) := by
    funext s
    simp only [Function.comp_apply,hcode s,compile_encode]
  exact ⟨he ▸ h⟩

/-- The exact two clock metadata fields used by the paper. -/
lemma outputCode_clock (m : ℕ) (tail : Str) :
    outputCode (4*(m+1)+1) tail = encNat (Main.clockQubits m)++encNat (Main.ell m)++tail := rfl

end QMAPerfectCompleteness.Uniformity.UnaryNextPowerTM

end

/- Inline helpers retained from Solutions.CyclicMetadataTM. -/
section


/-! Actual finite-plan extraction of unary verifier headers and HH count, retaining its body. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.CyclicMetadataTM
open QAlgorithms.Complexity (Str encNat)
open Uniformity

































theorem uniformOnVerifierCodes : ClassTransport.UniformOnVerifierCodes gatesG2 extract := by
  intro gen V hgen henc
  obtain ⟨hf⟩ := hgen
  refine ⟨BinaryComposition.computableContinuation (g := extract) hf (FinitePlanCompiler.machine config)
    (Equiv.refl Bool) (Equiv.refl Bool) timePolynomial ?_⟩
  intro x
  simpa only [Equiv.refl,List.map_id_fun,henc x,id_eq] using outputs_verifier (V x)

end QMAPerfectCompleteness.Main.CyclicMetadataTM

end

/- Inline helpers retained from Solutions.CyclicClockPrefixTM. -/
section


/-! A finite unary affine-header stage retaining the complete original input stream. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.CyclicClockPrefixTM
open QAlgorithms.Complexity (Str encNat)











































@[simp] lemma prepare_encode (m : ℕ) (tail : Str) : prepare (encNat m++tail)=outputCode m tail := by simp [prepare]

theorem polyTime_on_unary_prefix {f : Str → Str}
    (hf : QAlgorithms.Complexity.PolyTimeComputable f)
    (m : Str → ℕ) (payload : Str → Str) (hcode : ∀ s, f s=encNat (m s)++payload s) :
    QAlgorithms.Complexity.PolyTimeComputable (fun s => outputCode (m s) (payload s)) := by
  obtain ⟨hf⟩ := hf
  have h := BinaryComposition.computableContinuation (g := prepare) hf machine
    (Equiv.refl Bool) (Equiv.refl Bool) timePolynomial (fun s => by
      simp only [Equiv.refl,List.map_id_fun,id_eq]
      rw [hcode s,prepare_encode]
      exact outputs (m s) (payload s))
  have he : prepare ∘ f = fun s => outputCode (m s) (payload s) := by
    funext s
    simp only [Function.comp_apply,hcode s,prepare_encode]
  exact ⟨he ▸ h⟩

end QMAPerfectCompleteness.Uniformity.CyclicClockPrefixTM

end

/- Inline helpers retained from Solutions.CyclicClockMetadata. -/
section


/-! Actual polynomial-time generation of c,ell,m,a,out,HH and the original source body. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.CyclicMetadataTM
open QAlgorithms.Complexity (Str encNat)
open Uniformity



lemma code_split (V : Verifier gatesG2) : code V=encNat V.proofQubits++payload V := by
  simp only [code,payload,List.append_assoc]





@[simp] lemma clockExtract_encode (V : Verifier gatesG2) : clockExtract V.encode=clockCode V := by simp [clockExtract]

/-- Three actual machine stages: retained-body HH extraction, affine T prefix, next-power loop. -/
theorem clock_uniformOnVerifierCodes : ClassTransport.UniformOnVerifierCodes gatesG2 clockExtract := by
  intro gen V hgen henc
  have h0 := uniformOnVerifierCodes gen V hgen henc
  have h0' : QAlgorithms.Complexity.PolyTimeComputable (fun x => code (V x)) := by
    have he : (fun x => extract (gen x)) = (fun x => code (V x)) := by
      funext x
      rw [henc x,extract_encode]
    exact he ▸ h0
  have h1 := CyclicClockPrefixTM.polyTime_on_unary_prefix h0'
    (fun x => (V x).proofQubits) (fun x => payload (V x)) (fun x => code_split (V x))
  have h2 := UnaryNextPowerTM.polyTime_on_unary_prefix h1
    (fun x => 4*(V x).proofQubits+5) (fun x => code (V x)) (fun x => by
      simp only [CyclicClockPrefixTM.outputCode,code_split,List.append_assoc])
  have he : (fun x => UnaryNextPowerTM.outputCode (4*(V x).proofQubits+5) (code (V x))) =
      (fun x => clockCode (V x)) := by
    funext x
    rw [show 4*(V x).proofQubits+5=4*((V x).proofQubits+1)+1 by omega,
      UnaryNextPowerTM.outputCode_clock]
    rfl
  have h3 := he ▸ h2
  have he' : (fun x => clockExtract (gen x)) = (fun x => clockCode (V x)) := by
    funext x
    rw [henc x,clockExtract_encode]
  exact he'.symm ▸ h3

end QMAPerfectCompleteness.Main.CyclicMetadataTM

end

/- Inline helpers retained from Solutions.CyclicIndexMetadataCorrectness. -/
section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.CyclicIndexMetadataTM
open QAlgorithms.Complexity (Str encNat)
open StructuredStack StructuredStack.Code




















lemma values_eq (v : Values) : values (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)=v := by
  funext j; fin_cases j <;> rfl
@[simp] lemma compile_sourceCode (v : Values) (body : Str) :
    compile (sourceCode v body)=targetCode v body := by
  simp only [compile,sourceCode,List.append_assoc,Main.Encoding.parseNat_encode]
  rw [values_eq]

/-- A real finite TM computes all seven metadata fields with quadratic unary runtime. -/
theorem polyTime_on_six_fields {f : Str→Str} (hf : QAlgorithms.Complexity.PolyTimeComputable f)
    (v : Str→Values) (body : Str→Str) (hcode : ∀s,f s=sourceCode (v s) (body s)) :
    QAlgorithms.Complexity.PolyTimeComputable (fun s=>targetCode (v s) (body s)) := by
  obtain ⟨hf⟩ := hf
  have h := BinaryComposition.computableContinuation (g:=compile) hf machine
    (Equiv.refl Bool) (Equiv.refl Bool) timePolynomial (fun s=>by
      simp only [Equiv.refl,List.map_id_fun,id_eq]
      rw [hcode s,compile_sourceCode]
      exact outputs (v s) (body s))
  have he : compile ∘ f = fun s=>targetCode (v s) (body s) := by
    funext s; simp only [Function.comp_apply,hcode s,compile_sourceCode]
  exact ⟨he ▸ h⟩

end QMAPerfectCompleteness.Uniformity.CyclicIndexMetadataTM

end

/- Inline helpers retained from Solutions.CyclicFullMetadata. -/
section

/-! A closed actual polynomial-time compiler for all cyclic serializer parameters. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.CyclicMetadataTM
open QAlgorithms.Complexity (Str encNat)
open QMAPerfectCompleteness.Uniformity




lemma sourceCode_values (V : Verifier gatesG2) :
    CyclicIndexMetadataTM.sourceCode (metadataValues V) (sourceBody V)=clockCode V := by
  simp [CyclicIndexMetadataTM.sourceCode,metadataValues,CyclicIndexMetadataTM.values,
    clockCode,code,sourceBody,List.append_assoc]
lemma index_values (V : Verifier gatesG2) : CyclicIndexMetadataTM.index (metadataValues V)=indexQubits V := rfl


lemma targetCode_values (V : Verifier gatesG2) :
    CyclicIndexMetadataTM.targetCode (metadataValues V) (sourceBody V)=metadataCode V := by
  rw [CyclicIndexMetadataTM.targetCode,index_values,sourceCode_values]
  rfl

@[simp] lemma metadataExtract_encode (V : Verifier gatesG2) : metadataExtract V.encode=metadataCode V := by
  simp [metadataExtract]

/-- Every stage is witnessed by an actual finite TM2, including next-power and multiplication. -/
theorem metadata_uniformOnVerifierCodes : ClassTransport.UniformOnVerifierCodes gatesG2 metadataExtract := by
  intro gen V hgen henc
  have hc := clock_uniformOnVerifierCodes gen V hgen henc
  have he : (fun x=>clockExtract (gen x))=(fun x=>clockCode (V x)) := by
    funext x; rw [henc x,clockExtract_encode]
  have hc' := he ▸ hc
  have hi := CyclicIndexMetadataTM.polyTime_on_six_fields hc'
    (fun x=>metadataValues (V x)) (fun x=>sourceBody (V x))
    (fun x=>(sourceCode_values (V x)).symm)
  have he' : (fun x=>CyclicIndexMetadataTM.targetCode (metadataValues (V x)) (sourceBody (V x)))=
      (fun x=>metadataExtract (gen x)) := by
    funext x; rw [targetCode_values,henc x,metadataExtract_encode]
  exact he' ▸ hi

end QMAPerfectCompleteness.Main.CyclicMetadataTM

end

/- Inline helpers retained from Solutions.RecipeVerifierContext. -/
section


/-! The readonly serializer context of an actual verifier, bounded by its seven-field
metadata encoding rather than by an assumed polynomial-time output-size argument. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CircuitRecipe.Context
open QMAPerfectCompleteness.Uniformity.StructuredStack





@[simp] theorem ofMeta_environment (P : CyclicRaw.Meta) (src : List RawEncoding.Instruction) :
    inputEnvironment (ofMeta P src).values=P.env := rfl
@[simp] theorem ofMeta_context (P : CyclicRaw.Meta) (src : List RawEncoding.Instruction) :
    inputContext (ofMeta P src).values=[] := by simp [inputContext]


 



 



end QMAPerfectCompleteness.Main.CircuitRecipe.Context

end

/- Inline helpers retained from Solutions.CyclicProvisionalCode. -/
section


/-! Exact provisional encoding of the finite cyclic recipe, before the count-field pass. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.CyclicRecipe
open CircuitRecipe
open QAlgorithms.Complexity (Str encNat)



lemma provisionalCode_ofMeta (C : CircuitRecipe.Circuit) (P : CyclicRaw.Meta)
    (src : List RawEncoding.Instruction) :
    C.provisionalCode (Context.ofMeta P src)=
      encNat (C.eval P.env src).proofQubits++encNat (C.eval P.env src).ancillaQubits++
      encNat (C.eval P.env src).output++encNat 0++
        (C.eval P.env src).gates.flatMap RawEncoding.Instruction.encode := by
  simp only [Circuit.provisionalCode,Recipe.codeAt,Context.ofMeta_environment,
    Context.ofMeta_context,Circuit.eval]
  rfl

/-- The fixed finite recipe writes every real verifier header and literal gate byte exactly;
only the gate-count field is the deliberately zero placeholder. -/
theorem provisionalCode_ofVerifier (V : Verifier gatesG2) :
    program.provisionalCode (Context.ofVerifier V)=
      provisionalVerifierCode (CyclicVerifier.compileVerifier V) := by
  change program.provisionalCode (Context.ofMeta (CyclicRaw.params V) (RawEncoding.eraseVerifier V).gates)=_
  rw [provisionalCode_ofMeta]
  have h : program.eval (CyclicRaw.params V).env (RawEncoding.eraseVerifier V).gates=
      RawEncoding.eraseVerifier (CyclicVerifier.compileVerifier V) := compileRaw_erase V
  rw [h]
  simp only [provisionalVerifierCode,RawEncoding.eraseVerifier,List.flatMap_map,
    Function.comp_def,RawEncoding.eraseInstr_encode]


end QMAPerfectCompleteness.Main.CyclicRecipe

end

/- Inline helpers retained from Solutions.RecountGatesCorrectness. -/
section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.RecountGates
open QAlgorithms.Complexity (Str encNat)
open QMAPerfectCompleteness.Uniformity
open FinitePlanCompiler



















lemma parseBody_encode {n : ℕ} (gs : List (Instr gatesG2 n)) (fuel : ℕ) (hf : gs.length≤fuel) :
    parseBody n fuel (gs.flatMap Instr.encode)=some (gs.map RawEncoding.eraseInstr) := by
  induction gs generalizing fuel with
  | nil=>cases fuel <;> rfl
  | cons i gs ih=>
    cases fuel with
    | zero=>simp at hf
    | succ fuel=>
      have hn : i.encode++gs.flatMap Instr.encode≠[] := by
        intro he
        have hp:=instruction_length_pos i
        have hh:=congrArg List.length he
        simp only [List.length_append,List.length_nil] at hh
        omega
      have hf' : gs.length≤fuel := by simpa only [List.length_cons,Nat.add_le_add_iff_right] using hf
      simp [List.flatMap_cons,parseBody,hn,
        RawEncoding.parseInstruction_encode _ RawEncoding.g2Table_correct,ih fuel hf']


@[simp] lemma recount_provisional (V : Verifier gatesG2) : recount (provisionalCode V)=V.encode := by
  simpa [recount,provisionalCode,sourceHeader,List.append_assoc,
    parseBody_encode V.gates _ (gates_length_le V.gates),RawEncoding.eraseVerifier,-List.length_flatMap] using RawEncoding.eraseVerifier_encode V




/-- Correct the provisional count with an actual finite-machine polynomial continuation. -/
theorem polyTime_on_provisional {f : Str→Str} (hf : QAlgorithms.Complexity.PolyTimeComputable f)
    (V : Str→Verifier gatesG2) (hcode : ∀s,f s=provisionalCode (V s)) :
    QAlgorithms.Complexity.PolyTimeComputable (fun s=>(V s).encode) := by
  obtain ⟨hf⟩:=hf
  have h:=BinaryComposition.computableContinuation (g:=recount) hf (machine config)
    (Equiv.refl Bool) (Equiv.refl Bool) timePolynomial (fun s=>by
      simp only [Equiv.refl,List.map_id_fun,id_eq]
      rw [hcode s,recount_provisional]
      exact outputs_verifier (V s))
  have he : recount ∘ f=(fun s=>(V s).encode) := by funext s; simp [Function.comp_apply,hcode s]
  exact ⟨he ▸ h⟩
end QMAPerfectCompleteness.Main.RecountGates

end

/- Inline helpers retained from Solutions.RecipeSerializerContinuation. -/
section


/-! Close the serializer's actual finite-machine execution under a valid incoming metadata
producer. Parsing is total; no runtime claim on malformed input streams is needed. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace QMAPerfectCompleteness.Main.CircuitRecipe.Serializer
open QAlgorithms.Complexity (Str PolyTimeComputable)
open QMAPerfectCompleteness.Uniformity



@[simp] theorem decodeMetadata_verifier (V : Verifier gatesG2) :
    decodeMetadata (CyclicMetadataTM.metadataCode V)=
      some (CyclicRaw.params V,(RawEncoding.eraseVerifier V).gates) := by
  have hb := RecountGates.parseBody_encode V.gates _ (RecountGates.gates_length_le V.gates)
  simp only [decodeMetadata,CyclicMetadataTM.metadataCode,CyclicMetadataTM.clockCode,
    CyclicMetadataTM.code,List.append_assoc,Encoding.parseNat_encode,bind,Option.bind,Prod.fst,Prod.snd]
  rw [hb]
  simp only [CyclicRaw.params,CyclicRaw.ofRaw_erase]
  rfl



@[simp] theorem compile_verifier (g : Context 0 → Str) (V : Verifier gatesG2) :
    compile g (CyclicMetadataTM.metadataCode V)=g (Context.ofVerifier V) := by
  rw [compile,decodeMetadata_verifier]
  rfl

/-- A valid verifier-metadata generator followed by the literal serializer remains polynomial
in time; the output is exactly the writer's denotation on that verifier's context. -/
theorem polyTime_on_verifier_metadata {f : Str → Str} (hf : PolyTimeComputable f)
    (V : Str → Verifier gatesG2) (hcode : ∀ x,f x=CyclicMetadataTM.metadataCode (V x))
    {g : Context 0 → Str} (W : RecipeWriter 0 g) :
    PolyTimeComputable (fun x=>g (Context.ofVerifier (V x))) := by
  obtain ⟨hf⟩ := hf
  have h := BinaryComposition.computableContinuation (g := compile g) hf (machine W)
    (Equiv.refl Bool) (Equiv.refl Bool) (timePolynomial W) (fun x=>by
      simp only [Equiv.refl,List.map_id_fun,id_eq]
      rw [hcode x,compile_verifier]
      exact outputs_verifier W (V x))
  have he : compile g ∘ f=(fun x=>g (Context.ofVerifier (V x))) := by
    funext x
    simp [Function.comp_apply,hcode x]
  exact ⟨he ▸ h⟩

end QMAPerfectCompleteness.Main.CircuitRecipe.Serializer

end



/-! The paper's actual coherent-certificate circuit has a closed finite-machine polynomial
code generator. Metadata, bounded recipe evaluation, source traversal and gate recounting
are all witnessed by literal finite TM2 programs. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace QMAPerfectCompleteness.Main.CyclicRecipe
end QMAPerfectCompleteness.Main.CyclicRecipe
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CyclicRecipe
open CircuitRecipe
open ClassTransport
open QAlgorithms.Complexity (PolyTimeComputable)

/-- Continue any valid G₂ verifier generator with the exact coherent-certificate compiler. -/
theorem solution :
    UniformOnVerifierCodes gatesG2 executableCompile := by
  intro gen V hgen henc
  have hm := CyclicMetadataTM.metadata_uniformOnVerifierCodes gen V hgen henc
  have hmcode : ∀ x,CyclicMetadataTM.metadataExtract (gen x)=CyclicMetadataTM.metadataCode (V x) := by
    intro x
    rw [henc x,CyclicMetadataTM.metadataExtract_encode]
  have hp := Serializer.polyTime_on_verifier_metadata hm V hmcode
    (program.provisionalWriter SourceTM.sourceWriters)
  have hcount : ∀ x,program.provisionalCode (Context.ofVerifier (V x))=
      RecountGates.provisionalCode (CyclicVerifier.compileVerifier (V x)) := by
    intro x
    rw [provisionalCode_ofVerifier]
    simp only [provisionalVerifierCode,RecountGates.provisionalCode,
      QMAPerfectCompleteness.Uniformity.FinitePlanCompiler.sourceHeader,List.append_assoc]
  have hf := RecountGates.polyTime_on_provisional hp
    (fun x=>CyclicVerifier.compileVerifier (V x)) hcount
  have he : (fun x=>(CyclicVerifier.compileVerifier (V x)).encode)=
      (fun x=>executableCompile (gen x)) := by
    funext x
    rw [henc x,executableCompile_encode]
  exact he ▸ hf
