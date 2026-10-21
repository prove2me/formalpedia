-- Prove2me | solution 1 for OTCChain.Equilibrium.eq_64_Ns
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T21:48:55.822978+00:00
-- url     : https://prove2.me/submissions/402ee37f-9a93-4cb8-8b8c-38e95955a1de

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

open Set MeasureTheory OTCChain.Equilibrium

theorem solution (M : Params) (hM : M.Standing) (Δb Δs : ℝ) (h0 : 0 < Δb) (h1 : Δb < Δs)
    (h2 : Δs < M.Δbar) (μ : Densities) (hμ : IsSteadyState M Δb Δs μ) :
    μ.Ns M ^ 2 + (M.κ / M.lam + M.N - M.X - M.N * M.F Δs) * μ.Ns M
        - M.κ * M.X / M.lam * M.F Δs = 0 ∧
      μ.Ns M = NsOf M (M.F Δs) := by
  obtain ⟨hX, hXN, hlam, hκ, hr, hη, hη1, hc, hD, hf, hfi, hf1⟩ := hM
  obtain ⟨hnn, hib, his, hin, hih, h12, h14, h16, h18, h19⟩ := hμ
  have hNs : 0 ≤ μ.Ns M := by
    unfold Densities.Ns
    exact intervalIntegral.integral_nonneg hD.le (fun u hu => (hnn u hu).2.1)
  have hpos : 0 < M.κ + M.lam * μ.Ns M := by positivity
  set ch := (M.κ * M.X + M.lam * μ.Ns M * M.N) / (M.κ + M.lam * μ.Ns M) with hch
  -- pointwise form of μh above Δs
  have hhi : ∀ Δ ∈ Ioc Δs M.Δbar, μ.μh Δ = ch * M.f Δ := by
    intro Δ hΔ
    have hΔI : Δ ∈ Icc 0 M.Δbar := ⟨by linarith [hΔ.1], hΔ.2⟩
    obtain ⟨e1, e2, e3⟩ := h14 Δ hΔ
    have e4 := h12 Δ hΔI
    rw [e1, e2] at e4
    have hh : μ.μh Δ = M.N * M.f Δ - μ.μb Δ := by linarith
    have hb : μ.μb Δ * (M.κ + M.lam * μ.Ns M) = M.κ * (M.N - M.X) * M.f Δ := by nlinarith
    rw [hch, div_mul_eq_mul_div, eq_div_iff hpos.ne', hh]
    nlinarith
  -- integrability
  have hIh : ∀ a b, 0 ≤ a → a ≤ b → b ≤ M.Δbar → IntervalIntegrable μ.μh volume a b := by
    intro a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hih.mono_set (Icc_subset_Icc ha hb)
  have hIf : ∀ a b, 0 ≤ a → a ≤ b → b ≤ M.Δbar → IntervalIntegrable M.f volume a b := by
    intro a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hfi.mono_set (Icc_subset_Icc ha hb)
  have hlow : ∫ x in (0:ℝ)..Δs, μ.μh x = 0 := by
    have : ∫ x in (0:ℝ)..Δs, μ.μh x = ∫ x in (0:ℝ)..Δs, (0:ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Measure.ae_ne volume Δb, Measure.ae_ne volume Δs] with x hx1 hx2 hx
      rw [uIoc_of_le (by linarith)] at hx
      rcases lt_or_gt_of_ne hx1 with h | h
      · exact (h16 x ⟨hx.1.le, h⟩).2.1
      · exact (h18 x ⟨h, lt_of_le_of_ne hx.2 hx2⟩).2.1
    rw [this]; simp
  have hhigh : ∫ x in Δs..M.Δbar, μ.μh x = ch * (1 - M.F Δs) := by
    have : ∫ x in Δs..M.Δbar, μ.μh x = ∫ x in Δs..M.Δbar, ch * M.f x := by
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [uIoc_of_le h2.le] at hx
      exact hhi x hx
    rw [this, intervalIntegral.integral_const_mul]
    congr 1
    have := intervalIntegral.integral_interval_sub_left (hIf 0 M.Δbar le_rfl hD.le le_rfl)
      (hIf 0 Δs le_rfl (by linarith) h2.le)
    unfold Params.F
    rw [← hf1, ← this]
  have hH : ∫ x in (0:ℝ)..M.Δbar, μ.μh x = ch * (1 - M.F Δs) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hIh 0 Δs le_rfl (by linarith) h2.le)
      (hIh Δs M.Δbar (by linarith) h2.le le_rfl), hlow, hhigh, zero_add]
  have hsI : IntervalIntegrable μ.μs volume 0 M.Δbar := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hD.le]; exact his
  have hclear : μ.Ns M + ch * (1 - M.F Δs) = M.X := by
    rw [← h19, intervalIntegral.integral_add hsI (hIh 0 M.Δbar le_rfl hD.le le_rfl), hH]
    rfl
  have hF0 : 0 ≤ M.F Δs := by
    unfold Params.F
    exact intervalIntegral.integral_nonneg (by linarith) (fun u hu => hf u ⟨hu.1, by linarith [hu.2]⟩)
  have hquad : μ.Ns M ^ 2 + (M.κ / M.lam + M.N - M.X - M.N * M.F Δs) * μ.Ns M
        - M.κ * M.X / M.lam * M.F Δs = 0 := by
    rw [hch] at hclear
    field_simp at hclear
    field_simp
    linear_combination hclear
  refine ⟨hquad, ?_⟩
  set t := μ.Ns M
  set a := M.κ / M.lam + M.N - M.X - M.N * M.F Δs
  set q := M.κ * M.X / M.lam * M.F Δs
  have hq : 0 ≤ q := by positivity
  have hsq : (2 * t + a) ^ 2 = a ^ 2 + 4 * q := by linear_combination 4 * hquad
  unfold NsOf
  rw [show M.κ / M.lam + M.N - M.X - M.N * M.F Δs = a from rfl,
    show 4 * (M.κ * M.X / M.lam) * M.F Δs = 4 * q by ring]
  rcases le_or_gt 0 (2 * t + a) with hpa | hna
  · rw [← hsq, Real.sqrt_sq hpa]; ring
  · exfalso
    have hq0 : q ≤ 0 := by nlinarith
    have hq0' : q = 0 := le_antisymm hq0 hq
    have hF : M.F Δs = 0 := by
      have : M.κ * M.X / M.lam ≠ 0 := by positivity
      rcases mul_eq_zero.1 hq0' with h | h
      · exact absurd h this
      · exact h
    have : 0 < a := by
      show 0 < M.κ / M.lam + M.N - M.X - M.N * M.F Δs
      rw [hF]; have : 0 < M.κ / M.lam := by positivity
      linarith
    linarith
