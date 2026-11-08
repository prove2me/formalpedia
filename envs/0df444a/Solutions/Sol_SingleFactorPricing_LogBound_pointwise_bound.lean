-- Prove2me | solution 1 for SingleFactorPricing.LogBound.pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:17:26.788149+00:00
-- url     : https://prove2.me/submissions/7423d1c6-8f29-4f4a-9513-a32aff4cc0d7

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_filteredDemand
import Definitions.Def_SingleFactorPricing_LogBound_AssumptionA1
import Definitions.Def_SingleFactorPricing_LogBound_IsSingleFactorOptimum

open MeasureTheory

open SingleFactorPricing.LogBound in
theorem solution {N T : Type*} [Fintype N] [MeasurableSpace T] (μ : Measure T)
    (d : T → (N → ℝ) → N → ℝ) (f : N → ℝ) (pbar : T → N → ℝ) (Rf : ℝ)
    (hA1 : AssumptionA1 μ d f pbar) (hRf : IsSingleFactorOptimum μ d f Rf) (q : ℝ) (hq : 0 < q) :
    q * filteredDemand μ d f pbar q ≤ Rf := by
  have h1 : q * filteredDemand μ d f pbar q ≤ q * factorDemand μ d f q :=
    mul_le_mul_of_nonneg_left (hA1 q hq.le) hq.le
  have h2 : q * factorDemand μ d f q = aggregateProfit μ d (q • f) := by
    unfold factorDemand aggregateProfit typeProfit
    rw [← integral_const_mul]
    congr 1
    funext t
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have h3 : aggregateProfit μ d (q • f) ≤ Rf := hRf.1 ⟨q, hq, rfl⟩
  linarith
