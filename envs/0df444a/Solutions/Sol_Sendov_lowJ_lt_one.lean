-- Prove2me | solution 1 for Sendov.lowJ_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:08:42.881955+00:00
-- url     : https://prove2.me/submissions/e2a4e3f7-9e41-4a9d-9aa8-de104450f12a

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
import Theorems.Thm_Sendov_lowX_nonneg
import Theorems.Thm_Sendov_continuous_lowX_pow
import Theorems.Thm_Sendov_lowJ_four_lt_one
import Theorems.Thm_Sendov_pow_le_quartic_average
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {m : ℕ} (hm0 : 1 ≤ m) (hm4 : m ≤ 4) :
    lowJ m a < 1 := by
  have hcont4 := continuous_lowX_pow a 4
  have hcontm := continuous_lowX_pow a m
  have hmaj : Continuous fun t : ℝ => 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowX a t ^ 4 :=
    continuous_const.add (hcont4.const_mul _)
  have hint : (∫ t in (0 : ℝ)..1, (1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowX a t ^ 4))
      = 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowJ 4 a := by
    rw [intervalIntegral.integral_add (intervalIntegrable_const)
      ((hcont4.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul, lowJ]
    simp
  have hle : lowJ m a ≤ 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowJ 4 a := by
    rw [lowJ, ← hint]
    refine intervalIntegral.integral_mono_on (by norm_num) (hcontm.intervalIntegrable _ _)
      (hmaj.intervalIntegrable _ _) ?_
    intro u hu
    exact pow_le_quartic_average (lowX_nonneg (le_of_lt ha0) (le_of_lt ha1) hu.1) hm0 hm4
  have h4 := lowJ_four_lt_one ha0 ha1
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  nlinarith [hle, h4, hmpos]
end Sendov
