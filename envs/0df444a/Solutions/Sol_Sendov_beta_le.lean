-- Prove2me | solution 1 for Sendov.beta_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:15:31.492287+00:00
-- url     : https://prove2.me/submissions/ed0f36bd-6e1c-457c-89e0-9b54d0127ebe

import Definitions.Def_Sendov_Reduction_Polar
import Definitions.Def_Sendov_Common_Sinh
import Definitions.Def_Sendov_Reduction_BetaBound
import Theorems.Thm_Sendov_integral_exp_eq
import Theorems.Thm_Sendov_beta_lt_two
import Theorems.Thm_Sendov_log_sinh_div_le


set_option autoImplicit false
open Sendov
open MeasureTheory Real
variable {α B c : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 < α) (hB0 : 0 ≤ B)
    (hlt : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t))) : B ≤ α / (3 + α) := by
  have hB2 : B < 2 := beta_lt_two hα hlt
  rw [integral_exp_eq hα hB2] at hlt
  set u : ℝ := α * B / 2 with hudef
  set h : ℝ := α * (2 - B) / 2 with hhdef
  have hhpos : 0 < h := by
    rw [hhdef]
    have : 0 < 2 - B := by linarith
    positivity
  have hu0 : 0 ≤ u := by rw [hudef]; positivity
  -- `1 ≤ e^{-u} sinh h / h` is `e^u ≤ sinh h / h`
  have h1 : exp u ≤ sinh h / h := by
    rw [Real.exp_neg, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos u)] at hlt
    linarith
  have h2 : u ≤ Real.log (sinh h / h) := by
    rw [← Real.log_exp u]
    exact Real.log_le_log (Real.exp_pos u) h1
  have h3 : u ≤ Real.sqrt (h ^ 2 + 9) - 3 := h2.trans (log_sinh_div_le hhpos)
  -- square; `h = α - u`
  have hhu : h = α - u := by rw [hhdef, hudef]; ring
  have hsq : Real.sqrt (h ^ 2 + 9) ^ 2 = h ^ 2 + 9 := Real.sq_sqrt (by positivity)
  have h4 : (u + 3) ^ 2 ≤ h ^ 2 + 9 := by
    have hnn : (0 : ℝ) ≤ u + 3 := by linarith
    nlinarith [h3, hsq, Real.sqrt_nonneg (h ^ 2 + 9)]
  have h5 : u * (6 + 2 * α) ≤ α ^ 2 := by rw [hhu] at h4; nlinarith [h4]
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 3 + α)]
  rw [hudef] at h5
  nlinarith [h5, hα]
end Sendov
