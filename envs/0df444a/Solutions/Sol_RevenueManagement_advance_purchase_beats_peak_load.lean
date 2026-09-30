-- Prove2me | solution 1 for RevenueManagement.advance_purchase_beats_peak_load
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T22:37:24.797371+00:00
-- url     : https://prove2.me/submissions/55dc16e6-e92f-4e05-8e23-9b9bf923bd02

import Mathlib
import Definitions.Def_RevenueManagement_competition

open RevenueManagement

theorem solution (v C α wC : ℝ) (F f : ℝ → ℝ) (hα : 0 < α ∧ α < 1)
    (w2 wh : ℝ) (h2 : w2 ∈ Set.Icc 0 wC) (hw : wh ∈ Set.Icc 0 wC)
    (hf : ∀ w ∈ Set.Icc 0 wC, 0 < f w)
    (hψ : StrictAntiOn (fun w => (v - w) - F w / f w) (Set.Icc 0 wC))
    (h13 : (v - w2) * f w2 - F w2 = 1 / α - 1) (h15 : (v - wh) * f wh - F wh = 0)
    (hopt : ∀ w ∈ Set.Icc 0 wC, advancePurchaseRevenue v C α F w ≤ advancePurchaseRevenue v C α F wh) :
    w2 < wh ∧ peakLoadRevenue v C α F w2 ≤ advancePurchaseRevenue v C α F wh := by
  obtain ⟨hα0, hα1⟩ := hα
  have hf2 := hf w2 h2
  have hfh := hf wh hw
  -- ψ(w2) > 0 = ψ(wh)
  have hψ2 : 0 < (v - w2) - F w2 / f w2 := by
    have hpos : 0 < 1 / α - 1 := by rw [one_div, sub_pos]; exact one_lt_inv_iff₀.mpr ⟨hα0, hα1⟩
    have : (v - w2) - F w2 / f w2 = (1 / α - 1) / f w2 := by
      rw [← h13]; field_simp
    rw [this]; positivity
  have hψh : (v - wh) - F wh / f wh = 0 := by
    have : (v - wh) - F wh / f wh = ((v - wh) * f wh - F wh) / f wh := by field_simp
    rw [this, h15, zero_div]
  refine ⟨?_, ?_⟩
  · by_contra hle
    push Not at hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq] at hψh; linarith
    · have := hψ hw h2 hlt
      simp only at this
      linarith
  · have hpk : peakLoadRevenue v C α F w2 = advancePurchaseRevenue v C α F w2 - w2 * (1 - α) := by
      unfold peakLoadRevenue advancePurchaseRevenue; ring
    have := hopt w2 h2
    have hw2 : 0 ≤ w2 := h2.1
    rw [hpk]; nlinarith
