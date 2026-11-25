-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.integral_exp_mul_I_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:01:43.980517+00:00
-- url     : https://prove2.me/submissions/2eae9876-385b-48e2-808d-350b980747f8

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt

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
theorem _root_.solution {a b : ℕ} (hab : a ≠ b) :
    ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp ((((b : ℂ) - a) * I) * θ) = 0 := by
  have hc : ((b : ℂ) - a) * I ≠ 0 := by
    refine mul_ne_zero ?_ I_ne_zero
    rw [sub_ne_zero]; exact_mod_cast (Ne.symm hab)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
    (by linarith [Real.pi_pos]), integral_exp_mul_complex hc]
  have : Complex.exp (((b : ℂ) - a) * I * (Real.pi : ℝ)) =
      Complex.exp (((b : ℂ) - a) * I * ((-Real.pi : ℝ) : ℂ)) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨(b : ℤ) - a, ?_⟩
    push_cast; ring
  rw [this, sub_self, zero_div]
end ReciprocityTheory.GeometryOfNumbersTheory
