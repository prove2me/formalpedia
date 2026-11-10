-- Prove2me | solution 1 for QEC.Coding.BDL26RXCoarseInfluence.coarse_difference_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:44:56.493531+00:00
-- url     : https://prove2.me/submissions/de86d2f8-1df7-45e1-be3c-77fa393af57d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_coarse_eq_outside_influence

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCoarseInfluence
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (hi : 2 ≤ i.val) (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : FamilyQ S depth i.succ) :
    hammingSupport ((rxStepOutput S depth i h sigma).coarse.val +
      (rxStepOutput S depth i h (sigmaPlus S depth i sigma q)).coarse.val) ⊆
        influence S depth i h q := by
  intro z hz
  by_contra hnot
  have heq := coarse_eq_outside_influence S depth i h hi sigma q z hnot
  have hz0 : (rxStepOutput S depth i h sigma).coarse.val z +
      (rxStepOutput S depth i h (sigmaPlus S depth i sigma q)).coarse.val z ≠ 0 :=
    (Finset.mem_filter.mp hz).2
  apply hz0
  rw [← heq]
  exact ZModModule.add_self _
end QEC.Coding.BDL26RXCoarseInfluence
