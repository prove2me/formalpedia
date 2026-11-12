-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.localZWitnessInput_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:48:05.288619+00:00
-- url     : https://prove2.me/submissions/3e43b2be-9329-4e5c-837a-afab20d02eb0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_localZWitnessLower_val
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_indexedDecoderData_selected_rz
import Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_rzMap2_apply
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (S : OddScale) (x : BaseX)
    (f : DoubleCylinderFace baseTannerSquarePresentation x S) :
    (localZWitnessInput S).val (localZCoordinate S 0 x f) =
      BDL26UniformHistoryObstruction.lowerSyndromeRaw S 0 (.inl (.inl ⟨x, f⟩)) := by
  change ((indexedDecoderData S 2).selectedMap (1 : StepIndex 2)).map2
    (localZWitnessLower S).val (localZCoordinate S 0 x f) = _
  have hm := (indexedDecoderData_selected_rz S 2 (1 : StepIndex 2) (by decide)).2.2
  have he := eq_of_heq hm
  rw [he, localZWitnessLower_val]
  exact (BDL26OwnerParentObstruction.rzMap2_apply (state S 1).presentation
    (state S 1).admissible S (BDL26UniformHistoryObstruction.lowerSyndromeRaw S 0)
    (.inl (.inl ⟨x, f⟩))
    (BDL26RZMap1CoordinateBridge.rzMap1ZRoot (state S 1).presentation
      (state S 1).admissible (.inl (.inl ⟨x, f⟩)) S)).trans (if_pos rfl)
end QEC.Coding.BDL26CanonicalHistoryMarks
