-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.localZWitness_marked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:29:26.571572+00:00
-- url     : https://prove2.me/submissions/3df838c0-ddc4-4b93-a8d7-7c246ba5095b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_localZ_actual_guard
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_localZWitnessInput_coordinate
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_baseInput_depthTwo
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_input_layer
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (S : OddScale) :
    ∃ (x : BaseX) (f : DoubleCylinderFace baseTannerSquarePresentation x S),
      physicalNode S 0 0 (localZ S x f) ∈ marks S 0 (localZWitnessInput S) ∧
        parent S 1 (localZ S x f) = none := by
  let x : BaseX := BDL26UniformHistoryObstruction.retainedX S 0
  let origin : Fin S.half := ⟨0, S.half_pos⟩
  let f : DoubleCylinderFace baseTannerSquarePresentation x S :=
    .inl (0, BDL26UniformHistoryObstruction.retainedStarFace S 0, origin, origin)
  have hi : BDL26UniformRXTail.incidentStarFace S 0
      (BDL26UniformHistoryObstruction.retainedStarFace S 0) := Or.inl rfl
  have hl : BDL26UniformHistoryObstruction.lowerSyndromeRaw S 0 (.inl (.inl ⟨x, f⟩)) = 1 := by
    exact (BDL26UniformRXTail.lower_input_layer S 0
      (BDL26UniformHistoryObstruction.retainedStarFace S 0) 0 origin origin).trans
      (if_pos ⟨rfl, rfl, rfl, hi⟩)
  have hc : (localZWitnessInput S).val (localZCoordinate S 0 x f) ≠ 0 := by
    rw [localZWitnessInput_coordinate, hl]
    exact one_ne_zero
  have hb : (baseInput S 0 (localZWitnessInput S)).val (localZCoordinate S 0 x f) ≠ 0 := by
    rw [baseInput_depthTwo]
    exact hc
  have hactual : physicalNode S 0 0 (localZ S x f) ∈ marks S 0 (localZWitnessInput S) ∧
      parent S 1 (localZ S x f) = none :=
    localZ_actual_guard S 0 (localZWitnessInput S) x f hb
  exact ⟨x, f, hactual⟩
end QEC.Coding.BDL26CanonicalHistoryMarks
