-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.integral_conj_pow_mul_pow_mul_exp_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:14:28.232132+00:00
-- url     : https://prove2.me/submissions/16c92a5c-4082-4f47-885e-6808f526d16f

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integral_exp_mul_I_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory
open Set Complex
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {a b : ℕ} (hab : a ≠ b) (t : ℝ) :
    ∫ z : ℂ, starRingEnd ℂ (z ^ a) * z ^ b * (Real.exp (-(t * ‖z‖ ^ 2)) : ℂ) = 0 := by
  rw [integral_conj_pow_mul_pow_mul_exp_eq_polar, integral_exp_mul_I_of_ne hab, mul_zero]
end ReciprocityTheory.GeometryOfNumbersTheory
