-- Prove2me | solution 1 for TiltingFTT.Optimal.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:48:14.503685+00:00
-- url     : https://prove2.me/submissions/78c62940-b4b8-40b2-b17c-56a87b4131f0

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model
import Theorems.Thm_TiltingFTT_Optimal_tbar_deriv

open TiltingFTT.Optimal

namespace TFTT2Aux

lemma lin_aux (L R T : ℝ) (hLR : L ≤ R) (hR : 0 ≤ R) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    L * T ≤ R := by
  nlinarith [mul_nonneg hR (sub_nonneg.2 hT1), mul_nonneg (sub_nonneg.2 hLR) hT0]

lemma hD_pos (P : Firm) (hS : Standing P) (τ : ℝ) (hk : (1 + τ) * P.δU ≤ P.δI) :
    0 < P.δI * P.FLH - (1 + τ) * P.δU * P.FL := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
  have hFL : 0 < P.FL := by linarith
  have hδI : 0 < P.δI := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hk hFL.le, mul_lt_mul_of_pos_left h5 hδI]

/-- `δ_I F^H_L − k F_H ≤ T̄_L (δ_I − k) F_L` for `k ≤ δ_I`. -/
lemma key (P : Firm) (hS : Standing P) (τ : ℝ) (hτ : 0 ≤ τ) (hk : (1 + τ) * P.δU ≤ P.δI) :
    P.δI * P.FHL - (1 + τ) * P.δU * P.FH ≤ Tbar P τ * (P.δI - (1 + τ) * P.δU) * P.FL := by
  have hD := hD_pos P hS τ hk
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
  have hFL : 0 < P.FL := by linarith
  have hFH : 0 < P.FH := by linarith
  have hδI : 0 < P.δI := by linarith
  have hN : 0 ≤ (P.δI - (1 + τ) * P.δU) * P.FH := mul_nonneg (by linarith) hFH.le
  have htD : Tbar P τ * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL) =
      (P.δI - (1 + τ) * P.δU) * P.FH := by
    unfold Tbar; exact div_mul_cancel₀ _ hD.ne'
  have t0 : 0 ≤ Tbar P τ := div_nonneg hN hD.le
  generalize Tbar P τ = t at htD t0
  have hk0 : 0 ≤ P.δI - (1 + τ) * P.δU := by linarith
  rcases le_or_gt (P.δI * P.FHL - (1 + τ) * P.δU * P.FH) 0 with hX | hX
  · have := mul_nonneg (mul_nonneg t0 hk0) hFL.le
    linarith
  · have hX' : P.δI * P.FHL - (1 + τ) * P.δU * P.FH ≤ P.δI * P.FL - (1 + τ) * P.δU * P.FH := by
      nlinarith [mul_le_mul_of_nonneg_left (show P.FHL ≤ P.FL by linarith) hδI.le]
    have hD' : P.δI * P.FLH - (1 + τ) * P.δU * P.FL ≤ P.δI * P.FH - (1 + τ) * P.δU * P.FL := by
      nlinarith [mul_le_mul_of_nonneg_left (show P.FLH ≤ P.FH by linarith) hδI.le]
    have s1 := mul_le_mul_of_nonneg_right hX' hD.le
    have s2 := mul_le_mul_of_nonneg_left hD' (le_trans hX.le hX')
    have hk' : 0 ≤ P.δI * ((1 + τ) * P.δU) := mul_nonneg hδI.le (by positivity)
    have s3 : 0 ≤ P.δI * ((1 + τ) * P.δU) * (P.FH - P.FL) ^ 2 := mul_nonneg hk' (sq_nonneg _)
    have hXD : (P.δI * P.FHL - (1 + τ) * P.δU * P.FH) * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL)
        ≤ (t * (P.δI - (1 + τ) * P.δU) * P.FL) * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL) := by
      have e : (t * (P.δI - (1 + τ) * P.δU) * P.FL) * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL)
          = (P.δI - (1 + τ) * P.δU) * P.FL *
            (t * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL)) := by ring
      rw [e, htD]
      nlinarith
    exact le_of_mul_le_mul_right hXD hD

lemma tbar_nonneg (P : Firm) (hS : Standing P) (τ : ℝ) (hk : (1 + τ) * P.δU ≤ P.δI) :
    0 ≤ Tbar P τ := by
  have hD := hD_pos P hS τ hk
  have hFH : 0 < P.FH := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
    linarith
  exact div_nonneg (mul_nonneg (by linarith) hFH.le) hD.le

lemma tlow_le_tbar (P : Firm) (hS : Standing P) (τ : ℝ) (hτ : 0 ≤ τ)
    (hk : (1 + τ) * P.δU < P.δI) : Tlow P τ ≤ Tbar P τ := by
  have hFL : 0 < P.FL := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
    linarith
  have := key P hS τ hτ hk.le
  unfold Tlow
  rw [div_le_iff₀ (mul_pos (by linarith) hFL)]
  linarith

lemma tlow_lt_one (P : Firm) (hS : Standing P) (τ : ℝ) (hτ : 0 ≤ τ)
    (hk : (1 + τ) * P.δU < P.δI) : Tlow P τ < 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
  have hFL : 0 < P.FL := by linarith
  have hδI : 0 < P.δI := by linarith
  unfold Tlow
  rw [div_lt_one (mul_pos (by linarith) hFL)]
  have := mul_le_mul_of_nonneg_left (show P.FHL ≤ P.FL by linarith) hδI.le
  have := mul_pos (mul_pos (show (0:ℝ) < 1 + τ by linarith) h10) (sub_pos.2 h7)
  nlinarith

lemma char (P : Firm) (hS : Standing P) (τ : ℝ) (hτ : 0 ≤ τ)
    (hk : (1 + τ) * P.δU < P.δI) (TH TL : ℝ) :
    IsSeparatingEq P τ TH TL ↔
      TH = 1 ∧ max 0 (Tlow P τ) ≤ TL ∧ TL ≤ Tbar P τ ∧ TL < 1 := by
  have hD := hD_pos P hS τ hk.le
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
  have hFL : 0 < P.FL := by linarith
  have hFH : 0 < P.FH := by linarith
  have hak : 0 < P.δI - (1 + τ) * P.δU := by linarith
  have hN : 0 < (P.δI - (1 + τ) * P.δU) * P.FH := mul_pos hak hFH
  have hDL : 0 < (P.δI - (1 + τ) * P.δU) * P.FL := mul_pos hak hFL
  constructor
  · rintro ⟨⟨hTH0, hTH1⟩, ⟨hTL0, hTL1⟩, hne, hpH, hpL, hIC1, hIC2, hall⟩
    have hTH : TH = 1 := by
      by_contra hc
      have hlt : TH < 1 := lt_of_le_of_ne hTH1 hc
      by_cases hTL : TL = 1
      · have hT' : (TH + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
        have := (hall ((TH + 1) / 2) hT' (by intro h; linarith) (by intro h; linarith)).1
        nlinarith [mul_pos hN (show 0 < (TH + 1) / 2 - TH by linarith)]
      · have := (hall 1 ⟨zero_le_one, le_rfl⟩ (fun h => hc h.symm) (fun h => hTL h.symm)).1
        nlinarith [mul_pos hN (show 0 < 1 - TH by linarith)]
    subst hTH
    refine ⟨rfl, max_le hTL0 ?_, ?_, lt_of_le_of_ne hTL1 (fun h => hne h.symm)⟩
    · unfold Tlow
      rw [div_le_iff₀ hDL]
      linarith
    · unfold Tbar
      rw [le_div_iff₀ hD]
      linarith
  · rintro ⟨rfl, hlo, hhi, hlt1⟩
    have hTL0 : 0 ≤ TL := le_trans (le_max_left _ _) hlo
    have hTLlow : Tlow P τ ≤ TL := le_trans (le_max_right _ _) hlo
    have hIC1 : TL * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL) ≤ (P.δI - (1 + τ) * P.δU) * P.FH := by
      have := hhi; unfold Tbar at this; rwa [le_div_iff₀ hD] at this
    have hIC2 : P.δI * P.FHL - (1 + τ) * P.δU * P.FH ≤ TL * ((P.δI - (1 + τ) * P.δU) * P.FL) := by
      have := hTLlow; unfold Tlow at this; rwa [div_le_iff₀ hDL] at this
    have hR : 0 ≤ (P.δI - (1 + τ) * P.δU) * TL * P.FL := by
      have := mul_nonneg hTL0 hDL.le; linarith
    refine ⟨⟨zero_le_one, le_rfl⟩, ⟨hTL0, hlt1.le⟩, (ne_of_lt hlt1).symm, ?_, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · linarith
    · intro T' hT' _ _
      constructor
      · have := lin_aux _ _ T' (le_refl ((P.δI - (1 + τ) * P.δU) * P.FH)) hN.le hT'.1 hT'.2
        linarith
      · have := lin_aux (P.δI * P.FHL - (1 + τ) * P.δU * P.FH) ((P.δI - (1 + τ) * P.δU) * TL * P.FL)
          T' (by linarith) hR hT'.1 hT'.2
        linarith

end TFTT2Aux

open TFTT2Aux in
theorem solution (P : Firm) (τ : ℝ) (hS : Standing P) (hτ : 0 ≤ τ) :
    ((∃ TH TL, IsSeparatingEq P τ TH TL) ↔ Cond15 P τ) ∧
    ((1 + τ) * P.δU < P.δI →
      (∀ TH TL, IsSeparatingEq P τ TH TL ↔
        TH = 1 ∧ max 0 (Tlow P τ) ≤ TL ∧ TL ≤ Tbar P τ ∧ TL < 1) ∧
      Tlow P τ ≤ Tbar P τ ∧ Tlow P τ < 1 ∧
      (Cond17 P τ → Tbar P τ ≤ 1) ∧
      (P.δI * (P.FH - P.FLH) < (1 + τ) * P.δU * (P.FH - P.FL) → Tbar P τ < 1) ∧
      (¬ Cond17 P τ → 1 < Tbar P τ)) ∧
    StrictAntiOn (Tbar P) (Set.Icc 0 (tauFB P)) ∧
    StrictAntiOn (Tlow P) (Set.Ico 0 (tauFB P)) ∧
    P.δU * P.FL < P.δU * P.FH := by
  have hS' := hS
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS'
  have hFL : 0 < P.FL := by linarith
  have hFH : 0 < P.FH := by linarith
  have hδI : 0 < P.δI := by linarith
  have hkFB : ∀ x, x < tauFB P → (1 + x) * P.δU < P.δI := by
    intro x h
    unfold tauFB at h
    have : 1 + x < P.δI / P.δU := by linarith
    rwa [lt_div_iff₀ h10] at this
  refine ⟨?_, ?_, (tbar_deriv P hS).2, ?_, mul_lt_mul_of_pos_left h7 h10⟩
  · constructor
    · rintro ⟨TH, TL, hE⟩
      unfold Cond15
      by_contra hk
      rw [not_le] at hk
      obtain ⟨⟨hTH0, hTH1⟩, ⟨hTL0, hTL1⟩, hne, hpH, hpL, -, -, -⟩ := hE
      have a1 : TH ≤ 0 := by
        by_contra hc
        rw [not_le] at hc
        nlinarith [mul_pos (mul_pos hc hFH) (sub_pos.2 hk)]
      have a2 : TL ≤ 0 := by
        by_contra hc
        rw [not_le] at hc
        nlinarith [mul_pos (mul_pos hc hFL) (sub_pos.2 hk)]
      exact hne (by linarith)
    · intro hk
      unfold Cond15 at hk
      rcases lt_or_eq_of_le hk with hk | hk
      · refine ⟨1, max 0 (Tlow P τ), (char P hS τ hτ hk 1 _).2 ⟨rfl, le_rfl, ?_, ?_⟩⟩
        · exact max_le (tbar_nonneg P hS τ hk.le) (tlow_le_tbar P hS τ hτ hk)
        · exact max_lt zero_lt_one (tlow_lt_one P hS τ hτ hk)
      · refine ⟨1, 0, ⟨zero_le_one, le_rfl⟩, ⟨le_rfl, zero_le_one⟩, one_ne_zero, ?_, ?_, ?_, ?_, ?_⟩
        · rw [← hk]; ring_nf; exact le_rfl
        · ring_nf; exact le_rfl
        · rw [← hk]; ring_nf; exact le_rfl
        · rw [← hk]
          have : 0 ≤ (1 + τ) * P.δU * (P.FH - P.FHL) :=
            mul_nonneg (mul_nonneg (by linarith) h10.le) (by linarith)
          nlinarith
        · intro T' hT' _ _
          rw [← hk]
          constructor
          · ring_nf; exact le_rfl
          · have : 0 ≤ (1 + τ) * P.δU * (P.FH - P.FHL) * T' :=
              mul_nonneg (mul_nonneg (mul_nonneg (by linarith) h10.le) (by linarith)) hT'.1
            nlinarith
  · intro hk
    have hD := hD_pos P hS τ hk.le
    refine ⟨char P hS τ hτ hk, tlow_le_tbar P hS τ hτ hk, tlow_lt_one P hS τ hτ hk, ?_, ?_, ?_⟩
    · intro h17
      unfold Cond17 at h17
      unfold Tbar
      rw [div_le_one hD]
      linarith
    · intro h17
      unfold Tbar
      rw [div_lt_one hD]
      linarith
    · intro h17
      unfold Cond17 at h17
      rw [not_le] at h17
      unfold Tbar
      rw [one_lt_div hD]
      linarith
  · intro x hx y hy hxy
    have hkx := hkFB x hx.2
    have hky := hkFB y hy.2
    unfold Tlow
    rw [div_lt_div_iff₀ (mul_pos (by linarith) hFL) (mul_pos (by linarith) hFL)]
    have := mul_pos (mul_pos (mul_pos (mul_pos hδI (sub_pos.2 hxy)) h10)
      (show 0 < P.FH - P.FHL by linarith)) hFL
    nlinarith
