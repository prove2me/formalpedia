-- Prove2me | solution 1 for Sendov.beta_lt_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:59:57.650623+00:00
-- url     : https://prove2.me/submissions/d83a0769-c98e-45d2-98c1-5616dc197b76

import Definitions.Def_Sendov_Reduction_Polar
import Definitions.Def_Sendov_Common_Sinh
import Definitions.Def_Sendov_Reduction_BetaBound

set_option autoImplicit false
open Sendov
open MeasureTheory Real
variable {α B c : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 < α)
    (hlt : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t))) : B < 2 := by
  by_contra hcon
  rw [not_lt] at hcon
  have hmono : (∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t)))
      ≤ ∫ _t in (0 : ℝ)..1, exp (-α) := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((by fun_prop : Continuous fun t : ℝ =>
        exp (α * (-1 + (2 - B) * t))).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun _ : ℝ => exp (-α)).intervalIntegrable _ _) ?_
    intro u hu
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_nonneg (mul_nonneg hα.le hu.1) (sub_nonneg.2 hcon)]
  have hval : (∫ _t in (0 : ℝ)..1, exp (-α)) = exp (-α) := by simp
  have hone : exp (-α) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  rw [hval] at hmono
  linarith
end Sendov
