-- Prove2me | solution 1 for Sendov.integral_exp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:59:46.751805+00:00
-- url     : https://prove2.me/submissions/51eec20d-f00b-4a8d-aea5-69edfde9f3de

import Definitions.Def_Sendov_Reduction_Polar
import Definitions.Def_Sendov_Common_Sinh
import Definitions.Def_Sendov_Reduction_BetaBound
import Theorems.Thm_Sendov_integral_exp_mul

set_option autoImplicit false
open Sendov
open MeasureTheory Real
variable {α B c : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 < α) (hB : B < 2) :
    (∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t)))
      = exp (-(α * B / 2)) * (sinh (α * (2 - B) / 2) / (α * (2 - B) / 2)) := by
  have hkpos : 0 < α * (2 - B) := by
    have : 0 < 2 - B := by linarith
    positivity
  have hrw : ∀ t : ℝ, α * (-1 + (2 - B) * t) = -α + α * (2 - B) * t := by
    intro t; ring
  simp only [hrw, Real.exp_add]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul hkpos.ne' 0 1]
  simp only [mul_zero, Real.exp_zero]
  have hEF : exp (-(α * B / 2)) = exp (-α) * exp (α * (2 - B) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsq : exp (α * (2 - B) * 1) = exp (α * (2 - B) / 2) * exp (α * (2 - B) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hneg : exp (-(α * (2 - B) / 2)) = (exp (α * (2 - B) / 2))⁻¹ := Real.exp_neg _
  have hF : exp (α * (2 - B) / 2) ≠ 0 := (Real.exp_pos _).ne'
  rw [Real.sinh_eq, hEF, hsq, hneg]
  field_simp
end Sendov
