-- Prove2me | solution 1 for SingleFactorPricing.LogBound.aggregateProfit_factor_eq
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:15:29.523184+00:00
-- url     : https://prove2.me/submissions/f5afef0c-cd72-4ee0-9e72-170d0eb0901c

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_aggregateProfit
import Definitions.Def_SingleFactorPricing_LogBound_factorDemand

open MeasureTheory

open SingleFactorPricing.LogBound in
theorem solution {N T : Type*} [Fintype N] [MeasurableSpace T] (μ : Measure T)
    (d : T → (N → ℝ) → N → ℝ) (f : N → ℝ) (q : ℝ) :
    aggregateProfit μ d (q • f) = q * factorDemand μ d f q := by
  unfold aggregateProfit factorDemand typeProfit
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
