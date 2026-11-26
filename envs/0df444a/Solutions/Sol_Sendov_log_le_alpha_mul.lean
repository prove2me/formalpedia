-- Prove2me | solution 1 for Sendov.log_le_alpha_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:15:32.053049+00:00
-- url     : https://prove2.me/submissions/569786a7-0005-44c8-87bb-2f767573010a

import Definitions.Def_Sendov_Reduction_Polar
import Definitions.Def_Sendov_Common_Sinh
import Definitions.Def_Sendov_Reduction_BetaBound
import Theorems.Thm_P2M_Sendov_integral_exp_eq__5aea14f272a5

set_option autoImplicit false
open Sendov
open MeasureTheory Real
variable {α B c : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 < α) (hB1 : B ≤ 1)
    (hlt : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t))) :
    Real.log α ≤ α * (1 - B) := by
  have hB2 : B < 2 := by linarith
  rw [integral_exp_eq' hα hB2] at hlt
  have hden : (0 : ℝ) < α * (2 - B) := by
    have : (0 : ℝ) < 2 - B := by linarith
    positivity
  rw [le_div_iff₀ hden, one_mul] at hlt
  have hge : α ≤ α * (2 - B) := by nlinarith
  have hlt' : α < exp (α * (1 - B)) := by
    have := Real.exp_pos (-α)
    linarith
  exact (Real.log_le_iff_le_exp hα).2 hlt'.le
end Sendov
