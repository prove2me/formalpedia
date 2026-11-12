-- Prove2me | solution 1 for QEC.Coding.BDL26RXInfluenceBounds.coarse_difference_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:44:08.629379+00:00
-- url     : https://prove2.me/submissions/29af8e67-6595-4b28-b99b-7ee673c227a7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_errorInfluence_card_le
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_coarse_difference_support
import Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_coarse_difference_support
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXInfluenceBounds
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter BDL26RXCoarseInfluence BDL26BoundedValence
open BDL26GraphQuantitativeBounds BDL26RZMap1CoordinateBridge
open MultiscaleDecoder RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)
namespace QEC.Coding.BDL26RXInfluenceBounds
theorem _root_.solution (hi : 2 ≤ i.val)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (e : (indexedFamily S depth).Cochain1 i.succ) :
    HammingWeight ((rxStepOutput S depth i h sigma).coarse.val +
      (rxStepOutput S depth i h (sigmaPlusError S depth i sigma e)).coarse.val) ≤
        228 * HammingWeight e :=
  (Finset.card_le_card (coarse_difference_support S depth i h hi sigma e)).trans
    (errorInfluence_card_le S depth i h e)
end QEC.Coding.BDL26RXInfluenceBounds
