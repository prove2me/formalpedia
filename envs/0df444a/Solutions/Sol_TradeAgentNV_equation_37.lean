-- Prove2me | solution 1 for TradeAgentNV.equation_37
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:03:53.683245+00:00
-- url     : https://prove2.me/submissions/50768471-72b6-4e01-bff0-82167a1fb3cd

import Mathlib
import Definitions.Def_TradeAgentNV_rho
import Definitions.Def_TradeAgentNV_salesSupplyRatio

open MeasureTheory

open TradeAgentNV in
theorem solution
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (hU : Measurable U)
    (hU01 : ∀ᵐ ω ∂P, U ω ∈ Set.Icc (0 : ℝ) 1) (hEU : 0 < ∫ ω, U ω ∂P)
    (r t h π D q : ℝ) (hr : 0 < r) (ht : 0 < t) (hh : 0 < h) (hπ : 0 < π) (hD : 0 < D)
    (hq : 0 < q) (hrtπ : 0 < r - t + π) :
    h / rho r t h π < D / q →
      (∫ ω, min (U ω) (h / rho r t h π) ∂P) / (∫ ω, U ω ∂P) ≤ salesSupplyRatio P U D q ∧
        h / rho r t h π < salesSupplyRatio P U D q := by
  intro hka
  have hρ : 0 < rho r t h π := by unfold rho; linarith
  have hk1 : h / rho r t h π < 1 := by
    rw [div_lt_one hρ]; unfold rho; linarith
  have hint : ∀ c : ℝ, Integrable (fun ω => min (U ω) c) P := by
    intro c
    refine Integrable.of_bound (hU.min measurable_const).aestronglyMeasurable (max 1 |c|) ?_
    filter_upwards [hU01] with ω hω
    obtain ⟨h0, h1⟩ := hω
    rw [Real.norm_eq_abs, abs_le]
    have := neg_abs_le c
    have := le_max_left 1 |c|
    have := le_max_right 1 |c|
    constructor
    · exact le_min (by linarith) (by linarith)
    · exact (min_le_left _ _).trans (by linarith)
  have hintU : Integrable U P := by
    refine Integrable.of_bound hU.aestronglyMeasurable 1 ?_
    filter_upwards [hU01] with ω hω
    obtain ⟨h0, h1⟩ := hω
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  refine ⟨?_, ?_⟩
  · unfold salesSupplyRatio
    rw [div_le_div_iff_of_pos_right hEU]
    exact integral_mono (hint _) (hint _) (fun ω => min_le_min le_rfl hka.le)
  · unfold salesSupplyRatio
    rw [lt_div_iff₀ hEU]
    set k := h / rho r t h π with hkdef
    set a := D / q with hadef
    have ha : 0 < a := by positivity
    have hkm : k < min 1 a := lt_min hk1 hka
    have hmono : ∫ ω, min 1 a * U ω ∂P ≤ ∫ ω, min (U ω) a ∂P := by
      refine integral_mono_ae (hintU.const_mul _) (hint a) ?_
      filter_upwards [hU01] with ω hω
      obtain ⟨h0, h1⟩ := hω
      have e1 := min_le_left 1 a
      have e2 := min_le_right 1 a
      rcases le_total (U ω) a with hle | hle
      · rw [min_eq_left hle]; nlinarith
      · rw [min_eq_right hle]; nlinarith
    rw [integral_const_mul] at hmono
    have : k * ∫ ω, U ω ∂P < min 1 a * ∫ ω, U ω ∂P := mul_lt_mul_of_pos_right hkm hEU
    linarith
