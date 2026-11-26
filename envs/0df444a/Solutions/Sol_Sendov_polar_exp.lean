-- Prove2me | solution 1 for Sendov.polar_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:15:17.909808+00:00
-- url     : https://prove2.me/submissions/86b3d151-d210-4bdb-a499-302545f6ca9e

import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Reduction_Polar
import Theorems.Thm_Sendov_Ppolar_rpow_le
import Theorems.Thm_Sendov_M_pos
import Theorems.Thm_Sendov_continuous_Ppolar
import Theorems.Thm_Sendov_continuous_rpow_const


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x t α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) (hx : x ^ 2 ≤ 1) (hα : α = M n * (1 - a ^ 2) / 2)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2)) :
    1 ≤ ∫ t in (0 : ℝ)..1, Real.exp (α * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t)) := by
  have hM : (0 : ℝ) < M n := M_pos hn
  have he : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 := by simp only [M] at hM; linarith
  have hc1 : Continuous fun t : ℝ => Ppolar a x t ^ (((n : ℝ) - 1) / 2) :=
    (continuous_rpow_const he).comp (continuous_Ppolar a x)
  have hc2 : Continuous fun t : ℝ =>
      Real.exp (α * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t)) := by fun_prop
  refine hpolar.trans (intervalIntegral.integral_mono_on (by norm_num)
    (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _) ?_)
  intro u hu
  exact Ppolar_rpow_le hn hx hα hu.1 hu.2
end Sendov
