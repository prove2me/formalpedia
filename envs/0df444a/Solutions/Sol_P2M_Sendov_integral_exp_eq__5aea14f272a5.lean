-- Prove2me | solution 1 for P2M_Sendov_integral_exp_eq__5aea14f272a5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:59:51.987835+00:00
-- url     : https://prove2.me/submissions/966c066d-f8bc-41b2-b2a4-a0972ab19180

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
      = (exp (α * (1 - B)) - exp (-α)) / (α * (2 - B)) := by
  have hkpos : 0 < α * (2 - B) := by
    have : 0 < 2 - B := by linarith
    positivity
  have hrw : ∀ t : ℝ, α * (-1 + (2 - B) * t) = -α + α * (2 - B) * t := by
    intro t; ring
  simp only [hrw, Real.exp_add]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul hkpos.ne' 0 1]
  simp only [mul_zero, Real.exp_zero]
  have hsum : exp (-α) * exp (α * (2 - B) * 1) = exp (α * (1 - B)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← hsum]
  field_simp
end Sendov
