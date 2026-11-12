-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_mid_input_owner_marked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:19:22.745193+00:00
-- url     : https://prove2.me/submissions/e77d3a13-15ab-48c9-b4e8-706c38f736a6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_mid_input
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_aboveMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_marks_physical
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_outputAt_input
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_physicalMarks_step
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
attribute [local simp] QEC.Coding.BDL26CanonicalHistoryMarks.physicalMarks_step



set_option autoImplicit false
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
open QEC QEC.Coding QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale)
    (p : FamilyZ S 4 level3) (hp : (lower3 S).val p ≠ 0) :
    actualMidNode S (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) p) ∈
      BDL26CanonicalHistoryMarks.marks S 2 (upper4 S) := by
  have hi : (BDL26CanonicalHistoryMarks.outputAt S 2 (upper4 S)
      (0 : StepIndex 2)).input = lower3 S :=
    (BDL26CanonicalHistoryMarks.outputAt_input S 2 (upper4 S) (0 : StepIndex 2)).trans
      (actual_mid_input S)
  have hin : (BDL26CanonicalHistoryMarks.outputAt S 2 (upper4 S)
      (0 : StepIndex 2)).input.val p ≠ 0 := by
    intro hz
    exact hp ((congrArg (fun word : (CF S).Syndrome level3 => word.val p) hi).symm.trans hz)
  change BDL26CanonicalHistoryMarks.physicalNode S 2 (0 : StepIndex 2).succ
    (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) p) ∈
      BDL26CanonicalHistoryMarks.marks S 2 (upper4 S)
  apply (BDL26CanonicalHistoryMarks.mem_marks_physical S 2 (upper4 S)
    (0 : StepIndex 2).succ _).mpr
  rw [BDL26CanonicalHistoryMarks.physicalMarks_step]
  apply (BDL26CanonicalHistoryMarks.mem_aboveMarks S 2 (upper4 S) (0 : StepIndex 2) _).mpr
  exact Or.inl ⟨p,rfl,hin⟩
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
