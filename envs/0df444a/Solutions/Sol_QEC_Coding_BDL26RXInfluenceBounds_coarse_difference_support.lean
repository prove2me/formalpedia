-- Prove2me | solution 1 for QEC.Coding.BDL26RXInfluenceBounds.coarse_difference_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:19:40.146633+00:00
-- url     : https://prove2.me/submissions/5061b4aa-2fb9-4df9-9962-a54f648ad9d8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_coarse_eq_outside_errorInfluence

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
    hammingSupport ((rxStepOutput S depth i h sigma).coarse.val +
      (rxStepOutput S depth i h (sigmaPlusError S depth i sigma e)).coarse.val) ⊆
        errorInfluence S depth i h e := by
  intro z hz
  by_contra hnot
  have heq := coarse_eq_outside_errorInfluence S depth i h hi sigma e z hnot
  have hn := (Finset.mem_filter.mp hz).2
  apply hn
  change (rxStepOutput S depth i h sigma).coarse.val z +
    (rxStepOutput S depth i h (sigmaPlusError S depth i sigma e)).coarse.val z = 0
  rw [← heq]
  exact ZModModule.add_self _
end QEC.Coding.BDL26RXInfluenceBounds
