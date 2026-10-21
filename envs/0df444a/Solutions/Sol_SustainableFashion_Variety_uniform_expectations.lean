-- Prove2me | solution 1 for SustainableFashion.Variety.uniform_expectations
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:50:19.647824+00:00
-- url     : https://prove2.me/submissions/b900e1b1-55f0-4611-9521-10c875f312a2

import Mathlib
import Definitions.Def_SustainableFashion_Variety_Setting

set_option autoImplicit false
open MeasureTheory SustainableFashion.Variety

theorem solution (nbar q : ℝ) (hn : 0 < nbar) (hq0 : 0 ≤ q) (hq : q ≤ nbar) :
    (∫ n in (0 : ℝ)..nbar, n) / nbar = nbar / 2 ∧
    (∫ n in (0 : ℝ)..nbar, max (n - q) 0) / nbar = (nbar - q) ^ 2 / (2 * nbar) := by
  constructor
  · rw [integral_id]
    field_simp
    ring
  · have hint : IntervalIntegrable (fun n : ℝ => max (n - q) 0) volume 0 nbar :=
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    have h1 : ∫ n in (0 : ℝ)..q, max (n - q) 0 = 0 := by
      have : ∫ n in (0 : ℝ)..q, max (n - q) 0 = ∫ n in (0 : ℝ)..q, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hq0] at hx
        simp only
        exact max_eq_right (by linarith [hx.2])
      simpa using this
    have h2 : ∫ n in q..nbar, max (n - q) 0 = ∫ n in q..nbar, (n - q) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hq] at hx
      simp only
      exact max_eq_left (by linarith [hx.1])
    have h3 : ∫ n in q..nbar, (n - q) = (nbar - q) ^ 2 / 2 := by
      rw [intervalIntegral.integral_sub (by exact Continuous.intervalIntegrable (by fun_prop) _ _)
        (by exact Continuous.intervalIntegrable (by fun_prop) _ _)]
      simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (Continuous.intervalIntegrable (by fun_prop) 0 q)
      (Continuous.intervalIntegrable (by fun_prop) q nbar), h1, h2, h3]
    field_simp
    ring
