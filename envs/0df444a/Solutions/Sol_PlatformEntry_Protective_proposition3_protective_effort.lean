-- Prove2me | solution 1 for PlatformEntry.Protective.proposition3_protective_effort
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T21:44:26.092565+00:00
-- url     : https://prove2.me/submissions/37a06e6d-758f-485b-9b7a-59893f3ad211

import Mathlib
import Definitions.Def_PlatformEntry_Protective_Model

set_option autoImplicit false

namespace P3Protective04

theorem quad_id (m c a e t : ℝ) (ht : t * (2 * c - m) = m * a) :
    m * (a + t) ^ 2 / 2 - c * t ^ 2 - (m * (a + e) ^ 2 / 2 - c * e ^ 2) = (c - m / 2) * (e - t) ^ 2 := by
  linear_combination (e - t) * ht

theorem pN_le (m c a e t : ℝ) (h2 : 0 < 2 * c - m) (ht : t * (2 * c - m) = m * a) :
    m * (a + e) ^ 2 / 2 - c * e ^ 2 ≤ m * (a + t) ^ 2 / 2 - c * t ^ 2 := by
  have h := quad_id m c a e t ht
  have h' : 0 ≤ (c - m / 2) * (e - t) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  linarith

theorem pN_mono (m c a e d t : ℝ) (h2 : 0 < 2 * c - m) (ht : t * (2 * c - m) = m * a)
    (hed : e ≤ d) (hdt : d ≤ t) :
    m * (a + e) ^ 2 / 2 - c * e ^ 2 ≤ m * (a + d) ^ 2 / 2 - c * d ^ 2 := by
  have h1 := quad_id m c a e t ht
  have h2' := quad_id m c a d t ht
  have h3 : 0 ≤ (c - m / 2) * ((d - e) * (2 * t - e - d)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  nlinarith

theorem pE_le (k c a e w : ℝ) (hck : 0 < c - k) (hw : w * (c - k) = k * a) :
    k * (a + e) ^ 2 - c * e ^ 2 ≤ k * (a + w) ^ 2 - c * w ^ 2 := by
  have h : k * (a + w) ^ 2 - c * w ^ 2 - (k * (a + e) ^ 2 - c * e ^ 2) = (c - k) * (e - w) ^ 2 := by
    linear_combination 2 * (e - w) * hw
  have h' : 0 ≤ (c - k) * (e - w) ^ 2 := mul_nonneg hck.le (sq_nonneg _)
  linarith

theorem core (m c k Δ : ℝ) (hm0 : 0 ≤ m) (hmc : m < 2 * c) (hk0 : 0 ≤ k) (hkm : k ≤ m / 2)
    (hΔ : 0 ≤ Δ) (eN eE : ℝ → ℝ) (heN : ∀ a, eN a * (2 * c - m) = m * a)
    (heE : ∀ a, eE a * (c - k) = k * a) (T : ℝ → ℝ → ℝ)
    (hT1 : ∀ a e, e + a ≤ Δ → T a e = m * (a + e) ^ 2 / 2 - c * e ^ 2)
    (hT2 : ∀ a e, ¬ (e + a ≤ Δ) → T a e = k * (a + e) ^ 2 - c * e ^ 2) :
    ∃ a₁ ā₁ : ℝ, a₁ + eN a₁ = Δ ∧ a₁ ≤ ā₁ ∧ ∀ a : ℝ,
      (a ≤ a₁ → ∀ e', T a e' ≤ T a (eN a)) ∧
      (a₁ < a → a < ā₁ → ∀ e', T a e' ≤ T a (Δ - a)) ∧
      (ā₁ ≤ a → ∀ e', T a e' ≤ T a (eE a)) := by
  have hc : 0 < c := by linarith
  have h2 : 0 < 2 * c - m := by linarith
  have hck : 0 < c - k := by linarith
  have hTle : ∀ a e, T a e ≤ m * (a + e) ^ 2 / 2 - c * e ^ 2 := by
    intro a e
    by_cases h : e + a ≤ Δ
    · rw [hT1 a e h]
    · rw [hT2 a e h]
      have : 0 ≤ (m / 2 - k) * (a + e) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      linarith
  have hTge : ∀ a e, k * (a + e) ^ 2 - c * e ^ 2 ≤ T a e := by
    intro a e
    by_cases h : e + a ≤ Δ
    · rw [hT1 a e h]
      have : 0 ≤ (m / 2 - k) * (a + e) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      linarith
    · rw [hT2 a e h]
  obtain ⟨u, hu⟩ : ∃ u, c * u = (c - k) * Δ := ⟨(c - k) * Δ / c, by field_simp⟩
  have hu0 : 0 ≤ u := by
    by_contra hneg
    push Not at hneg
    have : c * u < 0 := mul_neg_of_pos_of_neg hc hneg
    nlinarith [mul_nonneg hck.le hΔ]
  obtain ⟨σ, hσ0, hσ⟩ : ∃ σ, 0 ≤ σ ∧ σ ^ 2 * (c - k) = m / 2 - k := by
    refine ⟨Real.sqrt ((m / 2 - k) / (c - k)), Real.sqrt_nonneg _, ?_⟩
    rw [Real.sq_sqrt (div_nonneg (by linarith) hck.le)]
    field_simp
  obtain ⟨a₁, ha₁⟩ : ∃ a₁, a₁ * (2 * c) = Δ * (2 * c - m) :=
    ⟨Δ * (2 * c - m) / (2 * c), by field_simp⟩
  have hpos : ∀ a, (eN a + a - Δ) * (2 * c - m) = 2 * c * (a - a₁) := by
    intro a
    linear_combination heN a + ha₁
  have hM : ∀ a, (c - k) * (m * (a + (Δ - a)) ^ 2 / 2 - c * (Δ - a) ^ 2)
      - (c - k) * (k * (a + eE a) ^ 2 - c * eE a ^ 2)
      = -c ^ 2 * ((a - u * (1 - σ)) * (a - u * (1 + σ))) := by
    intro a
    have hV : (c - k) * (k * (a + eE a) ^ 2 - c * eE a ^ 2) = k * c * a ^ 2 := by
      linear_combination (k * (a + eE a) - c * eE a) * heE a
    rw [hV]
    linear_combination (-2 * c * a + (c * u + (c - k) * Δ) * (1 - σ ^ 2)) * hu
      - (c - k) * Δ ^ 2 * hσ
  have hc2 : 0 < c ^ 2 := by positivity
  -- M(a) ≥ 0 iff the product is ≤ 0
  have hMge : ∀ a, (a - u * (1 - σ)) * (a - u * (1 + σ)) ≤ 0 →
      k * (a + eE a) ^ 2 - c * eE a ^ 2 ≤ m * (a + (Δ - a)) ^ 2 / 2 - c * (Δ - a) ^ 2 := by
    intro a hP
    have h := hM a
    have : 0 ≤ (c - k) * ((m * (a + (Δ - a)) ^ 2 / 2 - c * (Δ - a) ^ 2)
        - (k * (a + eE a) ^ 2 - c * eE a ^ 2)) := by
      have : 0 ≤ -c ^ 2 * ((a - u * (1 - σ)) * (a - u * (1 + σ))) := by nlinarith
      linarith
    by_contra hcon
    push Not at hcon
    have : (c - k) * ((m * (a + (Δ - a)) ^ 2 / 2 - c * (Δ - a) ^ 2)
        - (k * (a + eE a) ^ 2 - c * eE a ^ 2)) < 0 := mul_neg_of_pos_of_neg hck (by linarith)
    linarith
  have hMle : ∀ a, 0 ≤ (a - u * (1 - σ)) * (a - u * (1 + σ)) →
      m * (a + (Δ - a)) ^ 2 / 2 - c * (Δ - a) ^ 2 ≤ k * (a + eE a) ^ 2 - c * eE a ^ 2 := by
    intro a hP
    have h := hM a
    have : (c - k) * ((m * (a + (Δ - a)) ^ 2 / 2 - c * (Δ - a) ^ 2)
        - (k * (a + eE a) ^ 2 - c * eE a ^ 2)) ≤ 0 := by
      have : -c ^ 2 * ((a - u * (1 - σ)) * (a - u * (1 + σ))) ≤ 0 := by nlinarith
      linarith
    by_contra hcon
    push Not at hcon
    have : 0 < (c - k) * ((m * (a + (Δ - a)) ^ 2 / 2 - c * (Δ - a) ^ 2)
        - (k * (a + eE a) ^ 2 - c * eE a ^ 2)) := mul_pos hck (by linarith)
    linarith
  -- at a₁: eN a₁ = Δ - a₁, so M(a₁) ≥ 0
  have heN1 : eN a₁ = Δ - a₁ := by
    have h := hpos a₁
    have : (eN a₁ + a₁ - Δ) * (2 * c - m) = 0 := by rw [h]; ring
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · linarith
  have hP1 : (a₁ - u * (1 - σ)) * (a₁ - u * (1 + σ)) ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have hle := hMle a₁ hcon.le
    have hA := pN_le m c a₁ (eE a₁) (eN a₁) h2 (heN a₁)
    rw [heN1] at hA
    have hB : k * (a₁ + eE a₁) ^ 2 - c * eE a₁ ^ 2 ≤ m * (a₁ + eE a₁) ^ 2 / 2 - c * eE a₁ ^ 2 := by
      have : 0 ≤ (m / 2 - k) * (a₁ + eE a₁) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      linarith
    have heq : m * (a₁ + (Δ - a₁)) ^ 2 / 2 - c * (Δ - a₁) ^ 2 = k * (a₁ + eE a₁) ^ 2 - c * eE a₁ ^ 2 := by
      linarith
    have h := hM a₁
    rw [heq, sub_self] at h
    have : (a₁ - u * (1 - σ)) * (a₁ - u * (1 + σ)) = 0 := by
      have := h.symm
      have hc2' : c ^ 2 ≠ 0 := ne_of_gt hc2
      have : -c ^ 2 * ((a₁ - u * (1 - σ)) * (a₁ - u * (1 + σ))) = 0 := by linarith
      rcases mul_eq_zero.mp this with h'' | h''
      · exact absurd (neg_eq_zero.mp h'') hc2'
      · exact h''
    linarith
  have hr : u * (1 - σ) ≤ u * (1 + σ) := by nlinarith [mul_nonneg hu0 hσ0]
  have hr1 : u * (1 - σ) ≤ a₁ := by
    by_contra hcon
    push Not at hcon
    have : 0 < (a₁ - u * (1 - σ)) * (a₁ - u * (1 + σ)) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    linarith
  have hr2 : a₁ ≤ u * (1 + σ) := by
    by_contra hcon
    push Not at hcon
    have : 0 < (a₁ - u * (1 - σ)) * (a₁ - u * (1 + σ)) :=
      mul_pos (by linarith) (by linarith)
    linarith
  refine ⟨a₁, u * (1 + σ), ?_, hr2, fun a => ⟨?_, ?_, ?_⟩⟩
  · rw [heN1]; ring
  · intro ha e'
    have hle : eN a + a ≤ Δ := by
      have h := hpos a
      have : (eN a + a - Δ) * (2 * c - m) ≤ 0 := by rw [h]; nlinarith
      by_contra hcon
      push Not at hcon
      have : 0 < (eN a + a - Δ) * (2 * c - m) := mul_pos (by linarith) h2
      linarith
    rw [hT1 a (eN a) hle]
    exact le_trans (hTle a e') (pN_le m c a e' (eN a) h2 (heN a))
  · intro ha ha' e'
    have hlt : Δ - a ≤ eN a := by
      have h := hpos a
      have : 0 < (eN a + a - Δ) * (2 * c - m) := by rw [h]; nlinarith
      by_contra hcon
      push Not at hcon
      have : (eN a + a - Δ) * (2 * c - m) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) h2.le
      linarith
    rw [hT1 a (Δ - a) (by linarith)]
    by_cases h : e' + a ≤ Δ
    · rw [hT1 a e' h]
      exact pN_mono m c a e' (Δ - a) (eN a) h2 (heN a) (by linarith) hlt
    · rw [hT2 a e' h]
      have hP : (a - u * (1 - σ)) * (a - u * (1 + σ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      exact le_trans (pE_le k c a e' (eE a) hck (heE a)) (hMge a hP)
  · intro ha e'
    have hlt : Δ - a ≤ eN a := by
      have h := hpos a
      have : 0 ≤ (eN a + a - Δ) * (2 * c - m) := by rw [h]; nlinarith
      by_contra hcon
      push Not at hcon
      have : (eN a + a - Δ) * (2 * c - m) < 0 := mul_neg_of_neg_of_pos (by linarith) h2
      linarith
    have hP : 0 ≤ (a - u * (1 - σ)) * (a - u * (1 + σ)) :=
      mul_nonneg (by linarith) (by linarith)
    refine le_trans ?_ (hTge a (eE a))
    by_cases h : e' + a ≤ Δ
    · rw [hT1 a e' h]
      exact le_trans (pN_mono m c a e' (Δ - a) (eN a) h2 (heN a) (by linarith) hlt) (hMle a hP)
    · rw [hT2 a e' h]
      exact pE_le k c a e' (eE a) hck (heE a)

end P3Protective04

open PlatformEntry.Protective in
theorem solution (δ f β cS K : ℝ) (hbox : PlatformEntry.Regimes.InBox δ f β) (hcS : 1 / 2 < cS)
    (hK : 0 < K) (h5 : PlatformEntry.Regimes.cond5 δ f β) (hprot : PlatformEntry.Regimes.H δ f β ≤ 1 / 4) :
    (∃ a₁ ā₁ : ℝ, a₁ + eBN f cS a₁ = Delta δ f β K ∧ a₁ ≤ ā₁ ∧
      ∀ a : ℝ,
        (a ≤ a₁ → IsOptimalEffort δ f β cS K a (eBN f cS a)) ∧
        (a₁ < a → a < ā₁ → IsOptimalEffort δ f β cS K a (Delta δ f β K - a)) ∧
        (ā₁ ≤ a → IsOptimalEffort δ f β cS K a (eBE δ f β cS a))) ∧
    (∀ a e q : ℝ, PlatformEntry.Regimes.stage1Seller f cS a e q ≤ PlatformEntry.Regimes.stage1Seller f cS a e ((a + e) / 2)) := by
  obtain ⟨hδ0, hδ1, hf0, hf1, hβ0, hβ1⟩ := hbox
  have hH0 : 0 ≤ PlatformEntry.Regimes.H δ f β := by
    unfold PlatformEntry.Regimes.H
    split_ifs <;> positivity
  have hm0 : (0 : ℝ) ≤ 1 - f := by linarith
  have hkm : (1 / 4 + PlatformEntry.Regimes.H δ f β) * (1 - f) ≤ (1 - f) / 2 := by
    have := mul_le_mul_of_nonneg_right (show 1 / 4 + PlatformEntry.Regimes.H δ f β ≤ 1 / 2 by linarith) hm0
    linarith
  have heN : ∀ a, eBN f cS a * (2 * cS - (1 - f)) = (1 - f) * a := by
    intro a
    unfold eBN
    have hd : f + 2 * cS - 1 ≠ 0 := by
      have : 0 < f + 2 * cS - 1 := by linarith
      exact ne_of_gt this
    rw [show 2 * cS - (1 - f) = f + 2 * cS - 1 by ring]
    field_simp
  have heE : ∀ a, eBE δ f β cS a * (cS - (1 / 4 + PlatformEntry.Regimes.H δ f β) * (1 - f))
      = (1 / 4 + PlatformEntry.Regimes.H δ f β) * (1 - f) * a := by
    intro a
    unfold eBE
    have hd : 4 * cS - (1 - f) * (1 + 4 * PlatformEntry.Regimes.H δ f β) ≠ 0 := by
      have : 0 < 4 * cS - (1 - f) * (1 + 4 * PlatformEntry.Regimes.H δ f β) := by nlinarith
      exact ne_of_gt this
    field_simp
  have hT1 : ∀ a e, e + a ≤ Delta δ f β K →
      sellerTotal δ f β cS K a e = (1 - f) * (a + e) ^ 2 / 2 - cS * e ^ 2 := by
    intro a e h
    unfold sellerTotal PlatformEntry.Regimes.profitN
    rw [if_pos h]
  have hT2 : ∀ a e, ¬ (e + a ≤ Delta δ f β K) →
      sellerTotal δ f β cS K a e
        = (1 / 4 + PlatformEntry.Regimes.H δ f β) * (1 - f) * (a + e) ^ 2 - cS * e ^ 2 := by
    intro a e h
    unfold sellerTotal PlatformEntry.Regimes.profitE
    rw [if_neg h]
  refine ⟨?_, ?_⟩
  · obtain ⟨a₁, ā₁, h1, h2, h3⟩ := P3Protective04.core (1 - f) cS
      ((1 / 4 + PlatformEntry.Regimes.H δ f β) * (1 - f)) (Delta δ f β K) hm0 (by linarith)
      (mul_nonneg (by linarith) hm0) hkm (Real.sqrt_nonneg _) (eBN f cS) (eBE δ f β cS) heN heE
      (sellerTotal δ f β cS K) hT1 hT2
    exact ⟨a₁, ā₁, h1, h2, fun a =>
      ⟨fun h e' => (h3 a).1 h e', fun h h' e' => (h3 a).2.1 h h' e', fun h e' => (h3 a).2.2 h e'⟩⟩
  · intro a e q
    unfold PlatformEntry.Regimes.stage1Seller
    nlinarith [mul_nonneg hm0 (sq_nonneg ((a + e) / 2 - q))]
