-- Prove2me | solution 1 for StrictCQ.CAKKT.regNormal_eq_polar_tangentCone
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:44:40.751202+00:00
-- url     : https://prove2.me/submissions/65b111c1-536d-4aee-b2f2-80f5442822d0

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting

open Filter Topology
open scoped InnerProductSpace
open StrictCQ.CAKKT

theorem solution {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ S) :
    regNormal S z = StrictCQ.AGP.polar (tangentCone S z) := by
  ext w
  constructor
  · rintro ⟨-, hw⟩ d ⟨t, dk, ht, ht0, hd, hS⟩
    have hyz : Tendsto (fun k => z + t k • dk k) atTop (𝓝[S] z) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall hS⟩
      have h2 : Tendsto (fun k => z + t k • dk k) atTop (𝓝 (z + (0:ℝ) • d)) :=
        tendsto_const_nhds.add (ht0.smul hd)
      simpa using h2
    have key : ∀ ε > (0:ℝ), ⟪w, d⟫_ℝ ≤ ε * ‖d‖ := by
      intro ε hε
      have hev := hyz.eventually (hw ε hε)
      have hlim : Tendsto (fun k => ε * ‖dk k‖ - ⟪w, dk k⟫_ℝ) atTop (𝓝 (ε * ‖d‖ - ⟪w, d⟫_ℝ)) :=
        (tendsto_const_nhds.mul hd.norm).sub (tendsto_const_nhds.inner hd)
      have : 0 ≤ ε * ‖d‖ - ⟪w, d⟫_ℝ := by
        refine ge_of_tendsto hlim (hev.mono fun k hk => ?_)
        simp only [add_sub_cancel_left, inner_smul_right, norm_smul,
          Real.norm_eq_abs, abs_of_pos (ht k)] at hk
        have : t k * ⟪w, dk k⟫_ℝ ≤ t k * (ε * ‖dk k‖) := by linarith
        have := le_of_mul_le_mul_left this (ht k)
        linarith
      linarith
    by_contra hpos
    push Not at hpos
    have hdpos : 0 < ‖d‖ := by
      rcases eq_or_ne d 0 with h | h
      · simp [h] at hpos
      · exact norm_pos_iff.2 h
    have := key (⟪w, d⟫_ℝ / (2 * ‖d‖)) (by positivity)
    rw [div_mul_eq_mul_div, mul_comm (2:ℝ), ← div_div, mul_div_assoc, div_self hdpos.ne'] at this
    linarith
  · intro hw
    refine ⟨hz, fun ε hε => ?_⟩
    by_contra hne
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hne
    push Not at hne
    have hseq : ∀ k : ℕ, ∃ y, dist y z < 1 / ((k:ℝ) + 1) ∧ y ∈ S ∧
        ε * ‖y - z‖ < ⟪w, y - z⟫_ℝ := fun k => hne _ (by positivity)
    choose y hyd hyS hyi using hseq
    have hne0 : ∀ k, 0 < ‖y k - z‖ := by
      intro k
      rcases eq_or_ne (y k - z) 0 with h | h
      · have := hyi k; simp [h] at this
      · exact norm_pos_iff.2 h
    set u : ℕ → EuclideanSpace ℝ (Fin n) := fun k => ‖y k - z‖⁻¹ • (y k - z) with hu
    have hus : ∀ k, u k ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      intro k
      simp [hu, norm_smul, (hne0 k).ne']
    obtain ⟨d, hdS, φ, hφ, hlim⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).tendsto_subseq hus
    have hy0 : Tendsto (fun k => ‖y k - z‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => 1 / ((k:ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) h1
      rw [← dist_eq_norm]; exact (hyd k).le
    have hdT : d ∈ tangentCone S z := by
      refine ⟨fun k => ‖y (φ k) - z‖, fun k => u (φ k), fun k => hne0 _,
        hy0.comp hφ.tendsto_atTop, hlim, fun k => ?_⟩
      simp only [hu, smul_smul, mul_inv_cancel₀ (hne0 (φ k)).ne', one_smul, add_sub_cancel]
      exact hyS _
    have h1 := hw d hdT
    have h2 : ε ≤ ⟪w, d⟫_ℝ := by
      refine ge_of_tendsto ((tendsto_const_nhds.inner hlim)) (Eventually.of_forall fun k => ?_)
      simp only [Function.comp, hu, inner_smul_right]
      have := hyi (φ k)
      have hp := hne0 (φ k)
      calc ε = ‖y (φ k) - z‖⁻¹ * (ε * ‖y (φ k) - z‖) := by field_simp
        _ ≤ ‖y (φ k) - z‖⁻¹ * ⟪w, y (φ k) - z⟫_ℝ := by gcongr
    linarith
