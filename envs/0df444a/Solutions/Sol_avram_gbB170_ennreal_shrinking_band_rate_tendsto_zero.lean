-- Prove2me | solution 1 for avram_gbB170_ennreal_shrinking_band_rate_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:27:36.909198+00:00
-- url     : https://prove2.me/submissions/c208c805-2ae6-4a7d-a93e-1fa27b17bb8c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped ENNReal NNReal
noncomputable section

theorem solution (L : ℝ≥0) :
    Tendsto (fun k : ℕ =>
      ENNReal.ofReal ((L : ℝ) / ((k : ℝ) + 1)))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  have h : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1))
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hdiv : Tendsto
      (fun k : ℕ => (L : ℝ) / ((k : ℝ) + 1))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds.mul h)
  have hreal := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hdiv
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using hreal
