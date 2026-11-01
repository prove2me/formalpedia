-- Prove2me | solution 1 for ReferralPriority.Optimal.rFB_solves_A2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:15:41.301462+00:00
-- url     : https://prove2.me/submissions/0a739944-c37e-43d2-850e-b4da579a3148

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model

open ReferralPriority.Optimal

theorem solution (E : Env) (hS : E.Standing) (Lam : ℝ) (hL0 : 0 < Lam)
    (hL1 : Lam < E.mu - E.c / E.V) :
    0 < rFB E Lam ∧ rFB E Lam < 1 ∧ 0 < E.mu * (1 - rFB E Lam) - Lam ∧
      E.V - rFB E Lam * E.k - E.c / (E.mu * (1 - rFB E Lam) - Lam) = 0 := by
  obtain ⟨hmu, hc, hk, hV⟩ := hS
  have hV0 : 0 < E.V := lt_trans (div_pos hc hmu) hV
  have hVL : E.c < E.V * (E.mu - Lam) := by
    have : E.c / E.V < E.mu - Lam := by linarith
    rw [div_lt_iff₀ hV0] at this; linarith
  set Δ := 4 * E.k * E.mu * (E.c + Lam * E.V - E.mu * E.V) +
      (-E.k * Lam + E.k * E.mu + E.mu * E.V) ^ 2 with hΔ
  have hΔ' : Δ = (E.k * (E.mu - Lam) - E.mu * E.V) ^ 2 + 4 * E.k * E.mu * E.c := by
    rw [hΔ]; ring
  have hkm : 0 < E.k * E.mu := mul_pos hk hmu
  have hΔpos : 0 ≤ Δ := by rw [hΔ']; positivity
  set s := Real.sqrt Δ with hs_def
  have hs : s ^ 2 = Δ := Real.sq_sqrt hΔpos
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set B := -E.k * Lam + E.k * E.mu + E.mu * E.V with hB
  have hr : rFB E Lam * (2 * E.k * E.mu) = B - s := by
    simp only [rFB, hs_def, hΔ, hB]
    field_simp
    ring
  have hBpos : 0 < B := by
    rw [hB]; have : 0 < E.k * (E.mu - Lam) := by
      apply mul_pos hk; nlinarith [div_pos hc hV0]
    nlinarith [mul_pos hmu hV0]
  -- s < B
  have hsB : s < B := by
    have h1 : Δ < B ^ 2 := by
      rw [hΔ, hB]; nlinarith [mul_pos hkm (show 0 < E.V * (E.mu - Lam) - E.c by linarith)]
    nlinarith
  -- s > |µV - k(µ - Λ)|
  have hsT : E.mu * E.V - E.k * (E.mu - Lam) < s := by
    have h1 : (E.mu * E.V - E.k * (E.mu - Lam)) ^ 2 < s ^ 2 := by
      rw [hs, hΔ']; nlinarith [mul_pos hkm hc]
    nlinarith
  have h2 : 0 < 2 * E.k * E.mu := by positivity
  have hrpos : 0 < rFB E Lam := by
    have : 0 < rFB E Lam * (2 * E.k * E.mu) := by rw [hr]; linarith
    exact pos_of_mul_pos_left this h2.le
  have hD : 0 < E.mu * (1 - rFB E Lam) - Lam := by
    -- 2kµ·D = 2k(µ-Λ)·... : 2k * D = 2k(µ - Λ) - 2kµ r = 2k(µ-Λ) - (B - s)
    have : 2 * E.k * (E.mu * (1 - rFB E Lam) - Lam) = s - (E.mu * E.V - E.k * (E.mu - Lam)) := by
      have := hr; rw [hB] at this; nlinarith
    have h3 : 0 < 2 * E.k * (E.mu * (1 - rFB E Lam) - Lam) := by rw [this]; linarith
    exact pos_of_mul_pos_right h3 (by positivity)
  have hr1 : rFB E Lam < 1 := by
    by_contra h; push Not at h; nlinarith
  refine ⟨hrpos, hr1, hD, ?_⟩
  -- quadratic identity: (V - r k) D = c
  have hq : (E.V - rFB E Lam * E.k) * (E.mu * (1 - rFB E Lam) - Lam) = E.c := by
    set r := rFB E Lam
    have e : r = (B - s) / (2 * E.k * E.mu) := by field_simp; linarith
    rw [e]; field_simp
    rw [hB]; nlinarith [hs, hΔ]
  rw [sub_eq_zero, eq_div_iff hD.ne']
  exact hq
