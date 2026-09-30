-- Prove2me | solution 1 for RevenueManagement.duopoly_newsvendor_capacity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T22:37:24.273263+00:00
-- url     : https://prove2.me/submissions/527a2a6d-3bfe-4cfc-a2e4-843d5223b589

import Mathlib
import Definitions.Def_RevenueManagement_competition

open RevenueManagement MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (D1 D2 : Ω → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2) (c r : ℝ) (hc : 0 < c) (hcr : c < r)
    (xstar x1 x2 : ℝ) (hmono : P {ω | xstar < D1 ω + D2 ω} = ENNReal.ofReal (c / r))
    (hstrict : ∀ x, x < xstar → P {ω | xstar < D1 ω + D2 ω} < P {ω | x < D1 ω + D2 ω})
    (h1 : P {ω | effectiveDemand D1 D2 x2 ω ≤ x1} = ENNReal.ofReal (1 - c / r))
    (h2 : P {ω | effectiveDemand D2 D1 x1 ω ≤ x2} = ENNReal.ofReal (1 - c / r)) :
    xstar ≤ x1 + x2 := by
  by_contra hlt
  push Not at hlt
  have hr : 0 < r := hc.trans hcr
  have hcr1 : c / r ≤ 1 := (div_le_one hr).mpr hcr.le
  have hcr0 : 0 ≤ c / r := (div_pos hc hr).le
  -- R₁ is measurable
  have hR : Measurable (effectiveDemand D1 D2 x2) := by
    unfold effectiveDemand
    exact hD1.add ((hD2.sub_const x2).max measurable_const)
  have hS : MeasurableSet {ω | effectiveDemand D1 D2 x2 ω ≤ x1} :=
    measurableSet_le hR measurable_const
  -- {D > x₁ + x₂} ⊆ {R₁ > x₁}
  have hsub : {ω | x1 + x2 < D1 ω + D2 ω} ⊆ {ω | effectiveDemand D1 D2 x2 ω ≤ x1}ᶜ := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, effectiveDemand] at hω ⊢
    have := le_max_left (D2 ω - x2) 0
    linarith
  have hlt2 := hstrict (x1 + x2) hlt
  rw [hmono] at hlt2
  have hle := (measure_mono hsub).trans_lt' hlt2
  -- P(S) + P(Sᶜ) = 1
  have hsum := measure_add_measure_compl (μ := P) hS
  rw [measure_univ, h1] at hsum
  have hlt3 : ENNReal.ofReal (1 - c / r) + ENNReal.ofReal (c / r)
      < ENNReal.ofReal (1 - c / r) + P {ω | effectiveDemand D1 D2 x2 ω ≤ x1}ᶜ :=
    ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hle
  rw [hsum, ← ENNReal.ofReal_add (by linarith) hcr0] at hlt3
  simp at hlt3
