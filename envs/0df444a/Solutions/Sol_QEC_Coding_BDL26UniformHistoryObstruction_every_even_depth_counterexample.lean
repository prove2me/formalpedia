-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.every_even_depth_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:25:39.588196+00:00
-- url     : https://prove2.me/submissions/5a03a139-7be3-4d51-b314-f06833a95495

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_actualHistory_component_mask_counterexample

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (S : OddScale) (k : Nat) (hk : 2 ≤ k) :
    2 * (k - 2) + 4 = 2 * k ∧
    ∀ lower : Finset (StrictLowerNode S (k - 2)),
    ∃ p : FamilyZ S (2 * (k - 2) + 4) (TopIndex (2 * (k - 2) + 4)),
    ∃ hp : (upperSyndrome S (k - 2)).val p ≠ 0,
      maskWord (upperRegion S (k - 2) (component S (k - 2) lower p hp))
        (((indexedDecoderData S (2 * (k - 2) + 4)).selectedMap
          ⟨2 * (k - 2) + 3, by omega⟩).map2 (topOutput S (k - 2)).coarse.val) ≠
      ((indexedDecoderData S (2 * (k - 2) + 4)).selectedMap
        ⟨2 * (k - 2) + 3, by omega⟩).map2
        (maskWord (lowerRegion S (k - 2) (component S (k - 2) lower p hp))
          (topOutput S (k - 2)).coarse.val) :=
  ⟨by omega, actualHistory_component_mask_counterexample S (k - 2)⟩
end QEC.Coding.BDL26UniformHistoryObstruction
