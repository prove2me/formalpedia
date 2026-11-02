-- Prove2me | solution 1 for TiltingFTT.Optimal.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:51:53.374643+00:00
-- url     : https://prove2.me/submissions/08271661-0a59-4a2f-87b0-8cd3a6660089

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model

open TiltingFTT.Optimal

namespace TFTT3Aux

lemma lin_aux (L R T : ℝ) (hLR : L ≤ R) (hR : 0 ≤ R) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    L * T ≤ R := by
  nlinarith [mul_nonneg hR (sub_nonneg.2 hT1), mul_nonneg (sub_nonneg.2 hLR) hT0]

lemma fbar_bounds (P : Firm) (hS : Standing P) : P.FbL < Fbar P ∧ Fbar P < P.FbH := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
  unfold Fbar
  constructor
  · nlinarith [mul_pos h11 (sub_pos.2 h8)]
  · nlinarith [mul_pos (sub_pos.2 h12) (sub_pos.2 h8)]

set_option maxHeartbeats 1000000 in
/-- Characterization of pooling trades under (22). -/
lemma char (P : Firm) (hS : Standing P) (τ : ℝ) (hτ : 0 ≤ τ) (h22 : Cond22 P τ) (TP : ℝ) :
    IsPoolingEq P τ TP ↔ TlowP P τ ≤ TP ∧ TP ≤ 1 := by
  have hfb := fbar_bounds P hS
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
  obtain ⟨c1, c2⟩ := h22
  have hFL : 0 < P.FL := by linarith
  have hFH : 0 < P.FH := by linarith
  have hδI : 0 < P.δI := by linarith
  have hFb : 0 < Fbar P := by linarith
  have hk0 : 0 ≤ (1 + τ) * P.δU := by positivity
  have hka : (1 + τ) * P.δU < P.δI := by
    by_contra hc; rw [not_lt] at hc
    have := mul_le_mul_of_nonneg_right hc hFb.le
    have := mul_lt_mul_of_pos_left hfb.1 hδI
    linarith
  have hR1 : 0 < P.δI * P.FbH - (1 + τ) * P.δU * Fbar P := by
    have := mul_lt_mul_of_pos_left (show P.FbL < P.FbH by linarith) hδI
    linarith
  have hR2 : 0 ≤ P.δI * P.FbL - (1 + τ) * P.δU * Fbar P := by linarith
  have hN : 0 < (P.δI - (1 + τ) * P.δU) * P.FH := mul_pos (by linarith) hFH
  have hNR1 : (P.δI - (1 + τ) * P.δU) * P.FH ≤ P.δI * P.FbH - (1 + τ) * P.δU * Fbar P := by
    linarith
  -- X0 * R1 ≤ N * R2
  have hXR : (P.δI * P.FHL - (1 + τ) * P.δU * P.FH) * (P.δI * P.FbH - (1 + τ) * P.δU * Fbar P)
      ≤ (P.δI - (1 + τ) * P.δU) * P.FH * (P.δI * P.FbL - (1 + τ) * P.δU * Fbar P) := by
    have s1 : (P.δI * P.FHL - (1 + τ) * P.δU * P.FH) * (P.δI * P.FbH - (1 + τ) * P.δU * Fbar P)
        ≤ (P.δI * P.FbL - (1 + τ) * P.δU * P.FH) * (P.δI * P.FbH - (1 + τ) * P.δU * Fbar P) := by
      apply mul_le_mul_of_nonneg_right _ hR1.le
      nlinarith [mul_le_mul_of_nonneg_left h4 hδI.le]
    have e : (P.δI * P.FbL - (1 + τ) * P.δU * P.FH) * (P.δI * P.FbH - (1 + τ) * P.δU * Fbar P)
        - (P.δI - (1 + τ) * P.δU) * P.FH * (P.δI * P.FbL - (1 + τ) * P.δU * Fbar P)
        = P.δI ^ 2 * P.FbL * (P.FbH - P.FH) + P.δI * ((1 + τ) * P.δU) *
          (P.FH * Fbar P - P.FH * P.FbH + P.FH * P.FbL - P.FbL * Fbar P) := by ring
    have t1 : P.δI ^ 2 * P.FbL * (P.FbH - P.FH) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg _) (by linarith)) (by linarith)
    have t2 : P.δI ^ 2 * ((P.FbH - Fbar P) * (P.FbL - P.FH)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
    rcases le_or_gt (P.FH * Fbar P - P.FH * P.FbH + P.FH * P.FbL - P.FbL * Fbar P) 0 with hB | hB
    · have : P.δI * ((1 + τ) * P.δU) *
          (P.FH * Fbar P - P.FH * P.FbH + P.FH * P.FbL - P.FbL * Fbar P) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hδI.le hk0) hB
      linarith
    · have : P.δI * ((1 + τ) * P.δU) *
          (P.FH * Fbar P - P.FH * P.FbH + P.FH * P.FbL - P.FbL * Fbar P) ≤
          P.δI * P.δI * (P.FH * Fbar P - P.FH * P.FbH + P.FH * P.FbL - P.FbL * Fbar P) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hka.le hδI.le) hB.le
      nlinarith
  constructor
  · rintro ⟨⟨hTP0, hTP1⟩, -, -, hall⟩
    refine ⟨?_, hTP1⟩
    unfold TlowP
    rw [div_le_iff₀ hR1]
    by_cases h1' : TP = 1
    · subst h1'; linarith
    · have := (hall 1 ⟨zero_le_one, le_rfl⟩ (fun h => h1' h.symm)).1
      linarith
  · rintro ⟨hlo, hhi⟩
    have hlo' : (P.δI - (1 + τ) * P.δU) * P.FH ≤ TP * (P.δI * P.FbH - (1 + τ) * P.δU * Fbar P) := by
      unfold TlowP at hlo; rwa [div_le_iff₀ hR1] at hlo
    have hTP0 : 0 < TP := by
      by_contra hc; rw [not_lt] at hc
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hc hR1.le]
    refine ⟨⟨hTP0, hhi⟩, mul_nonneg (by linarith) hTP0.le, mul_nonneg (by linarith) hTP0.le, ?_⟩
    intro T' hT' _
    constructor
    · have := lin_aux ((P.δI - (1 + τ) * P.δU) * P.FH)
        ((P.δI * P.FbH - (1 + τ) * P.δU * Fbar P) * TP) T' (by linarith)
        (mul_nonneg hR1.le hTP0.le) hT'.1 hT'.2
      linarith
    · have hX : P.δI * P.FHL - (1 + τ) * P.δU * P.FH ≤
          (P.δI * P.FbL - (1 + τ) * P.δU * Fbar P) * TP := by
        have := mul_le_mul_of_nonneg_right hlo' hR2
        have h' : (P.δI * P.FHL - (1 + τ) * P.δU * P.FH) * (P.δI * P.FbH - (1 + τ) * P.δU * Fbar P)
            ≤ ((P.δI * P.FbL - (1 + τ) * P.δU * Fbar P) * TP) *
              (P.δI * P.FbH - (1 + τ) * P.δU * Fbar P) := by nlinarith
        exact le_of_mul_le_mul_right h' hR1
      have := lin_aux _ _ T' hX (mul_nonneg hR2 hTP0.le) hT'.1 hT'.2
      linarith

end TFTT3Aux

open TFTT3Aux in
set_option maxHeartbeats 1000000 in
theorem solution (P : Firm) (τ : ℝ) (hS : Standing P) (hτ : 0 ≤ τ) :
    ((∃ TP, IsPoolingEq P τ TP) ↔ Cond22 P τ) ∧
    (Cond22 P τ →
      0 < TlowP P τ ∧ ∀ TP, IsPoolingEq P τ TP ↔ TlowP P τ ≤ TP ∧ TP ≤ 1) ∧
    StrictAntiOn (TlowP P) (Set.Icc 0 (tauFB P)) := by
  have hfb := fbar_bounds P hS
  have hS' := hS
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS'
  have hFL : 0 < P.FL := by linarith
  have hFH : 0 < P.FH := by linarith
  have hδI : 0 < P.δI := by linarith
  have hFb : 0 < Fbar P := by linarith
  -- positivity of T̲_P under (22)
  have hpos : Cond22 P τ → 0 < TlowP P τ := by
    rintro ⟨c1, c2⟩
    have hka : (1 + τ) * P.δU < P.δI := by
      by_contra hc; rw [not_lt] at hc
      have := mul_le_mul_of_nonneg_right hc hFb.le
      have := mul_lt_mul_of_pos_left hfb.1 hδI
      linarith
    have hR1 : 0 < P.δI * P.FbH - (1 + τ) * P.δU * Fbar P := by
      have := mul_lt_mul_of_pos_left (show P.FbL < P.FbH by linarith) hδI
      linarith
    exact div_pos (mul_pos (by linarith) hFH) hR1
  refine ⟨?_, fun h22 => ⟨hpos h22, char P hS τ hτ h22⟩, ?_⟩
  · constructor
    · rintro ⟨TP, ⟨hTP0, hTP1⟩, hpH, hpL, hall⟩
      have hR1 : 0 ≤ -(1 + τ) * P.δU * Fbar P + P.δI * P.FbH :=
        (mul_nonneg_iff_of_pos_right hTP0).1 hpH
      have hR2 : 0 ≤ -(1 + τ) * P.δU * Fbar P + P.δI * P.FbL :=
        (mul_nonneg_iff_of_pos_right hTP0).1 hpL
      have hka : (1 + τ) * P.δU < P.δI := by
        by_contra hc; rw [not_lt] at hc
        have := mul_le_mul_of_nonneg_right hc hFb.le
        have := mul_lt_mul_of_pos_left hfb.1 hδI
        linarith
      have hN : 0 < (P.δI - (1 + τ) * P.δU) * P.FH := mul_pos (by linarith) hFH
      refine ⟨?_, by linarith⟩
      -- N ≤ R1
      suffices hs : (P.δI - (1 + τ) * P.δU) * P.FH ≤ P.δI * P.FbH - (1 + τ) * P.δU * Fbar P by
        linarith
      by_cases h1' : TP = 1
      · subst h1'
        by_contra hc; rw [not_le] at hc
        set N := (P.δI - (1 + τ) * P.δU) * P.FH with hNdef
        set R := P.δI * P.FbH - (1 + τ) * P.δU * Fbar P with hRdef
        have hR0 : 0 ≤ R := by rw [hRdef]; linarith
        have hq : N * (R / N) = R := mul_div_cancel₀ R hN.ne'
        have q0 : 0 ≤ R / N := div_nonneg hR0 hN.le
        have q1 : R / N < 1 := (div_lt_one hN).2 hc
        have := (hall ((1 + R / N) / 2) ⟨by linarith, by linarith⟩ (by intro h; linarith)).1
        have e : (P.δI * P.FH - (1 + τ) * P.δU * P.FH) * ((1 + R / N) / 2) =
            (N + N * (R / N)) / 2 := by rw [hNdef]; ring
        rw [e, hq] at this
        linarith
      · have := (hall 1 ⟨zero_le_one, le_rfl⟩ (fun h => h1' h.symm)).1
        have := mul_le_mul_of_nonneg_left hTP1 hR1
        linarith
    · intro h22
      exact ⟨1, (char P hS τ hτ h22 1).2 ⟨by
        have h := h22.1
        have hka : (1 + τ) * P.δU < P.δI := by
          by_contra hc; rw [not_lt] at hc
          have := mul_le_mul_of_nonneg_right hc hFb.le
          have := mul_lt_mul_of_pos_left hfb.1 hδI
          linarith [h22.2]
        have hR1 : 0 < P.δI * P.FbH - (1 + τ) * P.δU * Fbar P := by
          have := mul_lt_mul_of_pos_left (show P.FbL < P.FbH by linarith) hδI
          linarith [h22.2]
        unfold TlowP
        rw [div_le_one hR1]
        linarith, le_rfl⟩⟩
  · intro x hx y hy hxy
    have hkFB : ∀ z, z ≤ tauFB P → (1 + z) * P.δU ≤ P.δI := by
      intro z h
      unfold tauFB at h
      have : 1 + z ≤ P.δI / P.δU := by linarith
      rwa [le_div_iff₀ h10] at this
    have hkx := hkFB x hx.2
    have hky := hkFB y hy.2
    have hDpos : ∀ z, (1 + z) * P.δU ≤ P.δI → 0 < P.δI * P.FbH - (1 + z) * P.δU * Fbar P := by
      intro z hz
      have := mul_le_mul_of_nonneg_right hz hFb.le
      have := mul_lt_mul_of_pos_left hfb.2 hδI
      linarith
    unfold TlowP
    rw [div_lt_div_iff₀ (hDpos y hky) (hDpos x hkx)]
    have := mul_pos (mul_pos (mul_pos (mul_pos hδI (sub_pos.2 hxy)) h10)
      (show 0 < P.FbH - Fbar P by linarith)) hFH
    nlinarith
