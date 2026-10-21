-- Prove2me | solution 1 for OTCChain.Equilibrium.eq_65_66_Nb
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T21:50:10.510564+00:00
-- url     : https://prove2.me/submissions/bd06fba5-2b1f-430a-aa2e-330a911333b1

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

open Set MeasureTheory OTCChain.Equilibrium

theorem solution (M : Params) (hM : M.Standing) (Δb Δs : ℝ) (h0 : 0 < Δb) (h1 : Δb < Δs)
    (h2 : Δs < M.Δbar) (μ : Densities) (hμ : IsSteadyState M Δb Δs μ) :
    μ.Nb M ^ 2 + (M.κ / M.lam - M.N + M.X + M.N * M.F Δb) * μ.Nb M
        - M.κ / M.lam * (M.N - M.X) * (1 - M.F Δb) = 0 ∧
      μ.Nb M = NbOf M (M.F Δb) := by
  obtain ⟨hX, hXN, hlam, hκ, hr, hη, hη1, hc, hD, hf, hfi, hf1⟩ := hM
  obtain ⟨hnn, hib, his, hin, hih, h12, h14, h16, h18, h19⟩ := hμ
  have hNb : 0 ≤ μ.Nb M := by
    unfold Densities.Nb
    exact intervalIntegral.integral_nonneg hD.le (fun u hu => (hnn u hu).1)
  have hpos : 0 < M.κ + M.lam * μ.Nb M := by positivity
  set cn := (M.κ * (M.N - M.X) + M.lam * μ.Nb M * M.N) / (M.κ + M.lam * μ.Nb M) with hcn
  have hlo : ∀ Δ ∈ Ico 0 Δb, μ.μn Δ = cn * M.f Δ := by
    intro Δ hΔ
    have hΔI : Δ ∈ Icc 0 M.Δbar := ⟨hΔ.1, by linarith [hΔ.2]⟩
    obtain ⟨e1, e2, e3⟩ := h16 Δ hΔ
    have e4 := h12 Δ hΔI
    rw [e1, e2] at e4
    have hn : μ.μn Δ = M.N * M.f Δ - μ.μs Δ := by linarith
    have hs : μ.μs Δ * (M.κ + M.lam * μ.Nb M) = M.κ * M.X * M.f Δ := by nlinarith
    rw [hcn, div_mul_eq_mul_div, eq_div_iff hpos.ne', hn]
    nlinarith
  have hII : ∀ (g : ℝ → ℝ), IntegrableOn g (Icc 0 M.Δbar) →
      ∀ a b, 0 ≤ a → a ≤ b → b ≤ M.Δbar → IntervalIntegrable g volume a b := by
    intro g hg a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hg.mono_set (Icc_subset_Icc ha hb)
  have hlow : ∫ x in (0:ℝ)..Δb, μ.μn x = cn * M.F Δb := by
    have : ∫ x in (0:ℝ)..Δb, μ.μn x = ∫ x in (0:ℝ)..Δb, cn * M.f x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Measure.ae_ne volume Δb] with x hx1 hx
      rw [uIoc_of_le h0.le] at hx
      exact hlo x ⟨hx.1.le, lt_of_le_of_ne hx.2 hx1⟩
    rw [this, intervalIntegral.integral_const_mul]; rfl
  have hhigh : ∫ x in Δb..M.Δbar, μ.μn x = 0 := by
    have : ∫ x in Δb..M.Δbar, μ.μn x = ∫ x in Δb..M.Δbar, (0:ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Measure.ae_ne volume Δs] with x hx2 hx
      rw [uIoc_of_le (by linarith)] at hx
      rcases lt_or_gt_of_ne hx2 with h | h
      · exact (h18 x ⟨hx.1, h⟩).1
      · exact (h14 x ⟨h, hx.2⟩).1
    rw [this]; simp
  have hN : ∫ x in (0:ℝ)..M.Δbar, μ.μn x = cn * M.F Δb := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hII _ hin 0 Δb le_rfl h0.le (by linarith))
      (hII _ hin Δb M.Δbar h0.le (by linarith) le_rfl), hlow, hhigh, add_zero]
  have i := hII _ hib 0 M.Δbar le_rfl hD.le le_rfl
  have i2 := hII _ his 0 M.Δbar le_rfl hD.le le_rfl
  have i3 := hII _ hin 0 M.Δbar le_rfl hD.le le_rfl
  have i4 := hII _ hih 0 M.Δbar le_rfl hD.le le_rfl
  have htot : ∫ x in (0:ℝ)..M.Δbar, (μ.μs x + μ.μb x + μ.μn x + μ.μh x) = M.N := by
    rw [intervalIntegral.integral_congr (g := fun x => M.N * M.f x)
      (fun x hx => h12 x (by rwa [uIcc_of_le hD.le] at hx)), intervalIntegral.integral_const_mul,
      hf1, mul_one]
  have hsplit : ∫ x in (0:ℝ)..M.Δbar, (μ.μs x + μ.μb x + μ.μn x + μ.μh x)
      = (∫ x in (0:ℝ)..M.Δbar, (μ.μs x + μ.μh x)) + μ.Nb M + ∫ x in (0:ℝ)..M.Δbar, μ.μn x := by
    rw [intervalIntegral.integral_add ((i2.add i).add i3) i4,
      intervalIntegral.integral_add (i2.add i) i3, intervalIntegral.integral_add i2 i,
      intervalIntegral.integral_add i2 i4]
    unfold Densities.Nb; ring
  have hclear : μ.Nb M + cn * M.F Δb = M.N - M.X := by
    have := htot; rw [hsplit, h19, hN] at this; linarith
  have hquad : μ.Nb M ^ 2 + (M.κ / M.lam - M.N + M.X + M.N * M.F Δb) * μ.Nb M
        - M.κ / M.lam * (M.N - M.X) * (1 - M.F Δb) = 0 := by
    rw [hcn] at hclear
    field_simp at hclear
    field_simp
    linear_combination hclear
  refine ⟨hquad, ?_⟩
  have hF1 : M.F Δb ≤ 1 := by
    unfold Params.F
    rw [← hf1]
    apply intervalIntegral.integral_mono_interval le_rfl h0.le (by linarith)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hf x ⟨hx.1.le, hx.2⟩
    · exact hII _ hfi 0 M.Δbar le_rfl hD.le le_rfl
  set t := μ.Nb M
  set a := M.N - M.N * M.F Δb - M.X - M.κ / M.lam
  set q := M.κ / M.lam * (M.N - M.X) * (1 - M.F Δb)
  have hq : 0 ≤ q := by
    have : 0 ≤ 1 - M.F Δb := by linarith
    have : 0 < M.N - M.X := by linarith
    positivity
  have hsq : (2 * t - a) ^ 2 = a ^ 2 + 4 * q := by linear_combination 4 * hquad
  unfold NbOf
  rw [show M.N - M.N * M.F Δb - M.X - M.κ / M.lam = a from rfl,
    show 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - M.F Δb) = 4 * q by ring]
  rcases le_or_gt 0 (2 * t - a) with hpa | hna
  · rw [← hsq, Real.sqrt_sq hpa]; ring
  · exfalso
    have hq0 : q ≤ 0 := by nlinarith
    have hq0' : q = 0 := le_antisymm hq0 hq
    have hF : M.F Δb = 1 := by
      have : M.κ / M.lam * (M.N - M.X) ≠ 0 := by
        have : 0 < M.N - M.X := by linarith
        positivity
      rcases mul_eq_zero.1 hq0' with h | h
      · exact absurd h this
      · linarith
    have : a < 0 := by
      show M.N - M.N * M.F Δb - M.X - M.κ / M.lam < 0
      rw [hF]; have : 0 < M.κ / M.lam := by positivity
      linarith
    linarith
