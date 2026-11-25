-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_span_forms_of_isMultiHomogIdeal_934319068e0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:49.20451+00:00
-- url     : https://prove2.me/submissions/ea0cd58f-8d97-49bf-b3e6-3485a74f26a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K : Type} [DecidableEq K] {ι : K → Type}
    {R : Type*} [CommRing R] {P : Ideal (MRing ι R)} (hP : IsMultiHomogIdeal P) :
    Ideal.span {f | f ∈ P ∧ ∃ b, IsWeightedHomogeneous (blockWeight ι) f b} = P := by
  apply le_antisymm
  · rw [Ideal.span_le]
    exact fun f hf => hf.1
  · intro p hp
    rw [← sum_weightedHomogeneousComponent (w := blockWeight ι) p,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp p)]
    refine Ideal.sum_mem _ fun m _ => Ideal.subset_span ⟨hP p hp m, m, ?_⟩
    exact weightedHomogeneousComponent_isWeightedHomogeneous m p
end GroundTheory.Heights₂.Heights.NumbersDVR
