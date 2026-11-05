-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_lintegral_id_poissonMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:35:19.088704+00:00
-- url     : https://prove2.me/submissions/99650599-442b-470d-a5a3-ee94dce72479

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Theorems.Thm_ProbabilityTheory_poissonExpectation_hasSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal NNReal Nat
open MeasureTheory Real ProbabilityTheory

theorem solution (r : ℝ≥0) :
    ∫⁻ n, (n : ℝ≥0∞) ∂(poissonMeasure r) = (r : ℝ≥0∞) := by
  rw [lintegral_countable' (fun n : ℕ => (n : ℝ≥0∞))]
  have hsingle : ∀ n : ℕ, poissonMeasure r {n} =
      ENNReal.ofReal ((poissonMeasure r).real {n}) := by
    intro n
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hterm : ∀ n : ℕ, (n : ℝ≥0∞) * poissonMeasure r {n}
      = ENNReal.ofReal ((n : ℝ) * (poissonMeasure r).real {n}) := by
    intro n
    rw [hsingle, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (Nat.cast_nonneg n) measureReal_nonneg)
      (ProbabilityTheory.poissonExpectation_hasSum r).summable,
    (ProbabilityTheory.poissonExpectation_hasSum r).tsum_eq,
    ENNReal.ofReal_coe_nnreal]
