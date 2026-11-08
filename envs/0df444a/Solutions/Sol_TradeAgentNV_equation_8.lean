-- Prove2me | solution 1 for TradeAgentNV.equation_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:02:29.255062+00:00
-- url     : https://prove2.me/submissions/4c9bf6be-aa41-4d54-961c-aed4f2eee628

import Mathlib
import Definitions.Def_TradeAgentNV_expBenefit
import Definitions.Def_TradeAgentNV_salesSupplyRatio

open MeasureTheory

open TradeAgentNV in
theorem solution
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (hU : Measurable U)
    (hU01 : ∀ᵐ ω ∂P, U ω ∈ Set.Icc (0 : ℝ) 1) (hEU : 0 < ∫ ω, U ω ∂P)
    (r t h π D q : ℝ) (hr : 0 < r) (ht : 0 < t) (hh : 0 < h) (hπ : 0 < π) (hD : 0 < D)
    (hq : 0 < q) (hrtπ : 0 < r - t + π) :
    (0 < expBenefit P U r t h π D q ↔
        h / rho r t h π < (∫ ω, min (q * U ω) D ∂P) / (q * ∫ ω, U ω ∂P)) ∧
      (h / rho r t h π < (∫ ω, min (q * U ω) D ∂P) / (q * ∫ ω, U ω ∂P) ↔
        h / rho r t h π < salesSupplyRatio P U D q) := by
  have hρ : 0 < rho r t h π := by unfold rho; linarith
  have hqE : 0 < q * ∫ ω, U ω ∂P := mul_pos hq hEU
  constructor
  · unfold expBenefit
    rw [div_lt_div_iff₀ hρ hqE]
    constructor <;> intro H <;> nlinarith
  · have hA : ∫ ω, min (q * U ω) D ∂P = q * ∫ ω, min (U ω) (D / q) ∂P := by
      rw [← integral_const_mul]
      congr 1
      funext ω
      rw [mul_min_of_nonneg _ _ hq.le, mul_div_cancel₀ D hq.ne']
    unfold salesSupplyRatio
    rw [hA, mul_div_mul_left _ _ hq.ne']
