-- Prove2me | solution 1 for SuReturns.PartialRefunds.proposition1_ii_zero_salvage
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:11:37.366972+00:00
-- url     : https://prove2.me/submissions/0a6207d9-6102-4917-9715-3838b6a62bbf

import Mathlib
import Definitions.Def_SuReturns_PartialRefunds_Model

open MeasureTheory ProbabilityTheory

open SuReturns.PartialRefunds

theorem solution (ν D : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure D] (hν : Integrable (fun v => v) ν) (hν0 : ν (Set.Iio 0) = 0)
    (hD0 : D (Set.Iio 0) = 0) (c : ℝ) (hc : 0 < c) (hcμ : c < meanValuation ν) :
    ∀ p q, 0 ≤ q → fullRefundProfit ν D c 0 p q ≤ noReturnsProfit ν D c 0 q := by
  intro p q hq
  have hae : ∀ᵐ v ∂ν, 0 ≤ v := by
    rw [ae_iff]
    simpa [Set.Iio] using hν0
  have hi : Integrable ((Set.Ici p).indicator (fun _ : ℝ => p)) ν :=
    (integrable_const p).indicator measurableSet_Ici
  have hle : ∫ v, (Set.Ici p).indicator (fun _ : ℝ => p) v ∂ν ≤ ∫ v, v ∂ν := by
    apply integral_mono_ae hi hν
    filter_upwards [hae] with v hv
    by_cases h : v ∈ Set.Ici p
    · simpa only [Set.indicator_of_mem h] using (show p ≤ v from h)
    · simpa only [Set.indicator_of_notMem h] using hv
  have hp : p * keepProb ν p ≤ meanValuation ν := by
    simpa [integral_indicator measurableSet_Ici, integral_const, keepProb,
      meanValuation, measureReal_def, mul_comm] using hle
  have hd : 0 ≤ SupplyChainTheory.expSales D q := by
    apply integral_nonneg_of_ae
    have hd0 : ∀ᵐ x ∂D, 0 ≤ x := by
      rw [ae_iff]
      simpa [Set.Iio] using hD0
    filter_upwards [hd0] with x hx
    exact le_min hq hx
  simpa [fullRefundProfit, noReturnsProfit] using
    sub_le_sub_right (mul_le_mul_of_nonneg_right hp hd) (c*q)




#print axioms solution
