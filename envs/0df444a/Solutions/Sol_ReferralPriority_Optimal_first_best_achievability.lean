-- Prove2me | solution 1 for ReferralPriority.Optimal.first_best_achievability
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:21:01.219993+00:00
-- url     : https://prove2.me/submissions/483ec4bd-dd6e-4ac2-9c38-bbc047fe5204

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model
import Theorems.Thm_ReferralPriority_Optimal_rFB_solves_A2

open ReferralPriority.Optimal

theorem solution (E : Env) (hS : E.Standing) (Lam : ℝ) (hL0 : 0 < Lam)
    (hL1 : Lam < E.mu - E.c / E.V) :
    ((∃ W1 W0 : ℝ, SBFeasible E Lam W1 W0 (rFB E Lam) 1) ↔
        1 / (E.mu * (1 - rFB E Lam) - Lam * rFB E Lam) ≤ W1pp E Lam) ∧
      ∀ W1 W0 : ℝ, SBFeasible E Lam W1 W0 (rFB E Lam) 1 → W1 = W1pp E Lam ∧ W0 = W0pp E Lam := by
  obtain ⟨hr0, hr1, hD, hA2⟩ := rFB_solves_A2 E hS Lam hL0 hL1
  obtain ⟨hmu, hc, hkpos, hV⟩ := hS
  set r := rFB E Lam with hr_def
  set D := E.mu * (1 - r) - Lam with hD_def
  have hVr : (E.V - r * E.k) / E.c = 1 / D := by
    have : E.c / D = E.V - r * E.k := by linarith
    rw [← this]; field_simp
  have hW1pp : W1pp E Lam = 1 / D - E.k * (1 - r) / E.c := rfl
  have hW0pp : W0pp E Lam = 1 / D + E.k * r / E.c := rfl
  -- payoff formula at α = 1
  have hpay : ∀ W1 W0 r' : ℝ, payoff E W1 W0 1 r' =
      E.V - E.c * W0 - r' * (E.k + E.c * (W1 - W0)) := by
    intro W1 W0 r'; unfold payoff; ring
  -- uniqueness of the delays
  have huniq : ∀ W1 W0 : ℝ, SBFeasible E Lam W1 W0 r 1 → W1 = W1pp E Lam ∧ W0 = W0pp E Lam := by
    rintro W1 W0 ⟨⟨-, -, -, -, hIR, hOA, -, -, -⟩, hIC⟩
    have h0 := hIC 0 ⟨le_rfl, zero_le_one⟩
    have h1 := hIC 1 ⟨zero_le_one, le_rfl⟩
    rw [hpay, hpay] at h0 h1
    have hs : E.k + E.c * (W1 - W0) = 0 := by
      have a : r * (E.k + E.c * (W1 - W0)) ≤ 0 := by linarith
      have b : 0 ≤ (1 - r) * (E.k + E.c * (W1 - W0)) := by linarith
      have a' := (mul_nonpos_iff_pos_imp_nonpos.mp a).1 hr0
      have b' := (mul_nonneg_iff_of_pos_left (by linarith : (0:ℝ) < 1 - r)).mp b
      linarith
    have hW0 : W0 = W1 + E.k / E.c := by field_simp; linarith
    unfold IR at hIR; rw [hpay] at hIR
    unfold OA6a at hOA; simp only [mul_one] at hOA
    -- r W1 + (1-r) W0 = 1/D
    have hIR' : r * W1 + (1 - r) * W0 ≤ 1 / D := by
      rw [← hVr, le_div_iff₀ hc]; nlinarith
    have heq : r * W1 + (1 - r) * W0 = 1 / D := le_antisymm hIR' hOA
    rw [hW0] at heq
    have hW1 : W1 = 1 / D - E.k * (1 - r) / E.c := by
      field_simp at heq ⊢; linarith
    refine ⟨by rw [hW1pp]; exact hW1, ?_⟩
    rw [hW0pp, hW0, hW1]; field_simp; ring
  refine ⟨⟨?_, ?_⟩, huniq⟩
  · rintro ⟨W1, W0, hF⟩
    obtain ⟨e1, -⟩ := huniq W1 W0 hF
    have hb := hF.1.2.2.2.2.2.2.1
    unfold OA6b at hb; simp only [mul_one, one_pow] at hb
    rw [← e1]; exact hb
  · intro hA3
    have hDr : D ≤ E.mu * (1 - r) - Lam * r := by rw [hD_def]; nlinarith
    have hDpos : 0 < E.mu * (1 - r) - Lam * r := lt_of_lt_of_le hD hDr
    have hW1n : 0 ≤ W1pp E Lam := le_trans (by positivity) hA3
    have hsum : r * 1 * W1pp E Lam + (1 - r * 1) * W0pp E Lam = 1 / D := by
      rw [hW1pp, hW0pp]; field_simp; ring
    have hslope : E.k + E.c * (W1pp E Lam - W0pp E Lam) = 0 := by
      rw [hW1pp, hW0pp]; field_simp; ring
    have hpayc : ∀ r', payoff E (W1pp E Lam) (W0pp E Lam) 1 r' = 0 := by
      intro r'
      have : payoff E (W1pp E Lam) (W0pp E Lam) 1 r' = E.V - r * E.k - E.c * (r * 1 * W1pp E Lam + (1 - r * 1) * W0pp E Lam) := by
        unfold payoff
        have : W0pp E Lam = W1pp E Lam + E.k / E.c := by
          rw [hW1pp, hW0pp]; field_simp; ring
        rw [this]; field_simp; ring
      rw [this, hsum]
      have : E.c * (1 / D) = E.c / D := by ring
      rw [this]; linarith
    refine ⟨W1pp E Lam, W0pp E Lam, ⟨hW1n, ?_, ⟨hr0.le, hr1.le⟩, ⟨zero_le_one, le_rfl⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hW0pp]; have : 0 ≤ 1 / D := by positivity
      have : 0 ≤ E.k * r / E.c := by positivity
      linarith
    · unfold IR; rw [hpayc]
    · unfold OA6a; rw [hsum]; simp only [mul_one]; exact le_rfl
    · unfold OA6b; simp only [mul_one, one_pow]; exact hA3
    · unfold OA6c
      have h2 : 1 / (E.mu - Lam * 1) ≤ 1 / D := by
        apply one_div_le_one_div_of_le hD; rw [hD_def]; nlinarith
      rw [hW0pp]; have : 0 ≤ E.k * r / E.c := by positivity
      linarith
    · unfold Stable; simp only [mul_one]; linarith
    · intro r' _; rw [hpayc, hpayc]
