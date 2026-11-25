-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_sum_pairDiff_koszul_778ad1ac75eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:22.941842+00:00
-- url     : https://prove2.me/submissions/39470f42-4007-4d86-9ad7-05026e0bb64d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (M : Fin n → Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ)
    (hM : ∀ i j, M i j = -M j i) :
    ∑ i, pairDiff i * ∑ j, pairDiff j * M i j = 0 := by
  have h : ∑ i, pairDiff i * ∑ j, pairDiff j * M i j =
      -∑ i, pairDiff i * ∑ j, pairDiff j * M i j := by
    conv_lhs => simp only [Finset.mul_sum]; rw [Finset.sum_comm]
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hM j i]
    ring
  have h2 : (2 : MvPolynomial (Fin n ⊕ Fin n) ℤ) * ∑ i, pairDiff i * ∑ j, pairDiff j * M i j = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · exact h3
end GroundTheory.Heights₂.Heights.NumbersDVR
