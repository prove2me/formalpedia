-- Prove2me | solution 1 for TongString.virasoro_shapiro_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:30:21.289984+00:00
-- url     : https://prove2.me/submissions/6441d362-eab1-477a-86f1-cbf8db262510

import Theorems.Thm_TongString_vs_integral_beta_form
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

open Complex MeasureTheory TongString

theorem solution (a b c : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re)
    (habc : a + b + c = 1) :
    virasoroShapiroIntegral a b =
      2 * Real.pi * Gamma a * Gamma b * Gamma c /
        (Gamma (1 - a) * Gamma (1 - b) * Gamma (1 - c)) := by
  have hab : b + a = 1 - c := by linear_combination habc
  have hbeta :
      (∫ β in Set.Ioo (0 : ℝ) 1,
        ((1 - β : ℝ) : ℂ) ^ (a - 1) * (β : ℂ) ^ (b - 1)) =
      Gamma b * Gamma a / Gamma (b + a) := by
    rw [← betaIntegral_eq_Gamma_mul_div b a hb ha]
    simp only [betaIntegral, intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo, ofReal_sub, ofReal_one]
    apply integral_congr_ae
    filter_upwards [] with β
    exact mul_comm _ _
  rw [vs_integral_beta_form a b c ha hb hc habc, hbeta, hab]
  ring
