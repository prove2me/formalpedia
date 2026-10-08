-- Prove2me | solution 1 for RhinViola.unitIntervalMonomialLIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T11:26:14.103564+00:00
-- url     : https://prove2.me/submissions/3c4e034a-d3cd-4305-b6a7-1357a88a198b

import Theorems.Thm_RhinViola_unitIntervalMonomialIntegral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

theorem solution (n : ℕ) :
    (∫⁻ x : ℝ in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ n)) =
      ENNReal.ofReal ((1 : ℝ) / (((n + 1 : ℕ) : ℝ))) := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (intervalIntegral.intervalIntegrable_pow n).1,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    RhinViola.unitIntervalMonomialIntegral]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
  exact pow_nonneg hx.1.le n
