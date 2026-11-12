-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.not_actualHistory_component_mask_commutation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:35:16.0822+00:00
-- url     : https://prove2.me/submissions/67f910b3-85a0-44ca-8acb-cfa1b96a7934

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryComponentMask
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_actualHistory_component_mask_counterexample

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution (lower : Finset StrictLowerNode) :
    ¬ (∀ (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) (hp : witnessUpper.val p ≠ 0),
      maskWord (upperOwnerMaskRegion (componentWithLower lower p hp))
        (((indexedDecoderData scaleFive 4).selectedMap (3 : StepIndex 4)).map2 witnessTopOutput.coarse.val) =
      ((indexedDecoderData scaleFive 4).selectedMap (3 : StepIndex 4)).map2
        (maskWord (lowerOwnerMaskRegion (componentWithLower lower p hp)) witnessTopOutput.coarse.val)) := by
  intro h
  obtain ⟨p, hp, hn⟩ := actualHistory_component_mask_counterexample lower
  exact hn (h p hp)
end QEC.Coding.BDL26OwnerIncidenceMasks
