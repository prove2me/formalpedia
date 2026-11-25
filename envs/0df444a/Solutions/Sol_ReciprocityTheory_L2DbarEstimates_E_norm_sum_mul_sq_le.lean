-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.norm_sum_mul_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:03:41.950689+00:00
-- url     : https://prove2.me/submissions/83f4b735-b568-437d-a386-1bdc6d914dd9

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HalfSumNormSubSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open scoped ComplexConjugate
namespace ReciprocityTheory.L2DbarEstimates.E
theorem _root_.solution {n : ℕ} (a c : Fin n → ℂ) :
    ‖∑ j, a j * c j‖ ^ 2 ≤ (∑ j, ‖c j‖ ^ 2) * ∑ j, ‖a j‖ ^ 2 := by
  have h1 : ‖∑ j, a j * c j‖ ≤ ∑ j, ‖c j‖ * ‖a j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, mul_comm]
  have h2 : (∑ j, ‖c j‖ * ‖a j‖) ^ 2 ≤ (∑ j, ‖c j‖ ^ 2) * ∑ j, ‖a j‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
end ReciprocityTheory.L2DbarEstimates.E
