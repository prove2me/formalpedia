-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.norm_sum_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:02:06.131065+00:00
-- url     : https://prove2.me/submissions/e574417b-ccd6-4564-b798-b5ec1c91e338

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
theorem _root_.solution {n : ℕ} (a : Fin n → ℂ) :
    ‖∑ j, a j‖ ^ 2 = (∑ j, ∑ k, a j * conj (a k)).re := by
  have h : (∑ j, ∑ k, a j * conj (a k)) = (∑ j, a j) * conj (∑ j, a j) := by
    rw [map_sum, Finset.sum_mul_sum]
  rw [h, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
end ReciprocityTheory.L2DbarEstimates.E
