-- Prove2me | solution 1 for TiltingFTT.Optimal.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:41:24.047228+00:00
-- url     : https://prove2.me/submissions/c57935d2-49b2-4ce1-81cf-ae4570392c58

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model
import Theorems.Thm_TiltingFTT_Optimal_tauStar_step
import Theorems.Thm_TiltingFTT_Optimal_tau0_step
import Theorems.Thm_TiltingFTT_Optimal_tbar_deriv
import Theorems.Thm_TiltingFTT_Optimal_welfare_24_25

open TiltingFTT.Optimal

namespace TFTT6Aux

lemma lin_aux (L R T : ℝ) (hLR : L ≤ R) (hR : 0 ≤ R) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    L * T ≤ R := by
  nlinarith [mul_nonneg hR (sub_nonneg.2 hT1), mul_nonneg (sub_nonneg.2 hLR) hT0]

lemma fbar_bounds (P : Firm) (hS : Standing P) : P.FbL < Fbar P ∧ Fbar P < P.FbH := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
  unfold Fbar
  constructor
  · nlinarith [mul_pos h11 (sub_pos.2 h8)]
  · nlinarith [mul_pos (sub_pos.2 h12) (sub_pos.2 h8)]

lemma le_tauFB_iff (P : Firm) (hS : Standing P) (τ : ℝ) :
    τ ≤ tauFB P ↔ (1 + τ) * P.δU ≤ P.δI := by
  have h10 : 0 < P.δU := hS.2.2.2.2.2.2.2.2.2.1
  unfold tauFB
  rw [← le_div_iff₀ h10]
  constructor <;> intro h <;> linarith

lemma tauFB_lt_iff (P : Firm) (hS : Standing P) (τ : ℝ) :
    tauFB P < τ ↔ P.δI < (1 + τ) * P.δU := by
  have h10 : 0 < P.δU := hS.2.2.2.2.2.2.2.2.2.1
  unfold tauFB
  rw [← div_lt_iff₀ h10]
  constructor <;> intro h <;> linarith

lemma tauStar_lt_iff (P : Firm) (hS : Standing P) (τ : ℝ) :
    tauStar P < τ ↔ P.δI * P.FbL < (1 + τ) * P.δU * Fbar P := by
  have h10 : 0 < P.δU := hS.2.2.2.2.2.2.2.2.2.1
  have hFb : 0 < Fbar P := by
    have := (fbar_bounds P hS).1
    have : 0 < P.FbL := by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
      linarith
    linarith
  unfold tauStar
  have e : P.δI / P.δU * (P.FbL / Fbar P) = (P.δI * P.FbL) / (P.δU * Fbar P) := by
    rw [div_mul_div_comm]
  rw [e]
  have hp : 0 < P.δU * Fbar P := mul_pos h10 hFb
  constructor
  · intro h
    have h' : P.δI * P.FbL / (P.δU * Fbar P) < 1 + τ := by linarith
    rw [div_lt_iff₀ hp] at h'
    linarith
  · intro h
    have h' : P.δI * P.FbL / (P.δU * Fbar P) < 1 + τ := by
      rw [div_lt_iff₀ hp]; linarith
    linarith

/-- `(T_H, T_L) = (1, T̄_L(τ))` is a separating equilibrium for `τ ∈ (0, τ_FB]`. -/
lemma sepEq_tbar (P : Firm) (hS : Standing P) (h0 : Coexist P 0) (τ : ℝ) (hτ0 : 0 < τ)
    (hτFB : (1 + τ) * P.δU ≤ P.δI) : IsSeparatingEq P τ 1 (Tbar P τ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
  have hFL : 0 < P.FL := by linarith
  have hFH : 0 < P.FH := by linarith
  have hδI : 0 < P.δI := by linarith
  have hD : 0 < P.δI * P.FLH - (1 + τ) * P.δU * P.FL := by
    nlinarith [mul_le_mul_of_nonneg_right hτFB hFL.le, mul_lt_mul_of_pos_left h5 hδI]
  have hN : 0 ≤ (P.δI - (1 + τ) * P.δU) * P.FH := mul_nonneg (by linarith) hFH.le
  have htD : Tbar P τ * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL) =
      (P.δI - (1 + τ) * P.δU) * P.FH := by
    unfold Tbar; exact div_mul_cancel₀ _ hD.ne'
  have t0 : 0 ≤ Tbar P τ := div_nonneg hN hD.le
  have hND : (P.δI - (1 + τ) * P.δU) * P.FH < P.δI * P.FLH - (1 + τ) * P.δU * P.FL := by
    have c17 := h0.2.2
    unfold Cond17 at c17
    have := mul_pos (mul_pos hτ0 h10) (sub_pos.2 h7)
    nlinarith
  have t1 : Tbar P τ < 1 := (div_lt_one hD).2 hND
  generalize Tbar P τ = t at htD t0 t1
  have hk0 : 0 ≤ P.δI - (1 + τ) * P.δU := by linarith
  -- key inequality (IC2): δ_I F^H_L − (1+τ)δ_U F_H ≤ t (δ_I − (1+τ)δ_U) F_L
  have key : P.δI * P.FHL - (1 + τ) * P.δU * P.FH ≤ t * (P.δI - (1 + τ) * P.δU) * P.FL := by
    rcases le_or_gt (P.δI * P.FHL - (1 + τ) * P.δU * P.FH) 0 with hX | hX
    · have := mul_nonneg (mul_nonneg t0 hk0) hFL.le
      linarith
    · have hX' : P.δI * P.FHL - (1 + τ) * P.δU * P.FH ≤ P.δI * P.FL - (1 + τ) * P.δU * P.FH := by
        nlinarith [mul_le_mul_of_nonneg_left (show P.FHL ≤ P.FL by linarith) hδI.le]
      have hD' : P.δI * P.FLH - (1 + τ) * P.δU * P.FL ≤ P.δI * P.FH - (1 + τ) * P.δU * P.FL := by
        nlinarith [mul_le_mul_of_nonneg_left (show P.FLH ≤ P.FH by linarith) hδI.le]
      have s1 := mul_le_mul_of_nonneg_right hX' hD.le
      have s2 := mul_le_mul_of_nonneg_left hD' (le_trans hX.le hX')
      have hk : 0 ≤ P.δI * ((1 + τ) * P.δU) := mul_nonneg hδI.le (by positivity)
      have s3 : 0 ≤ P.δI * ((1 + τ) * P.δU) * (P.FH - P.FL) ^ 2 := mul_nonneg hk (sq_nonneg _)
      have hXD : (P.δI * P.FHL - (1 + τ) * P.δU * P.FH) * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL)
          ≤ (t * (P.δI - (1 + τ) * P.δU) * P.FL) * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL) := by
        have e : (t * (P.δI - (1 + τ) * P.δU) * P.FL) * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL)
            = (P.δI - (1 + τ) * P.δU) * P.FL *
              (t * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL)) := by ring
        rw [e, htD]
        nlinarith
      exact le_of_mul_le_mul_right hXD hD
  refine ⟨⟨zero_le_one, le_rfl⟩, ⟨t0, t1.le⟩, (ne_of_lt t1).symm, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · have := mul_nonneg (mul_nonneg t0 hk0) hFL.le
    linarith
  · linarith
  · linarith
  · intro T' hT' _ _
    constructor
    · have := lin_aux ((P.δI - (1 + τ) * P.δU) * P.FH) ((P.δI - (1 + τ) * P.δU) * P.FH) T'
        le_rfl hN hT'.1 hT'.2
      linarith
    · have := lin_aux (P.δI * P.FHL - (1 + τ) * P.δU * P.FH) (t * (P.δI - (1 + τ) * P.δU) * P.FL)
        T' key (mul_nonneg (mul_nonneg t0 hk0) hFL.le) hT'.1 hT'.2
      linarith

/-- Every separating equilibrium at `τ ≤ τ_FB` has welfare at most `W_S(τ)`. -/
lemma sep_bound (P : Firm) (hS : Standing P) (τ : ℝ) (hτFB : (1 + τ) * P.δU ≤ P.δI)
    (TH TL : ℝ) (h : IsSeparatingEq P τ TH TL) : sepWelfare P τ TH TL ≤ WS P τ := by
  obtain ⟨⟨hTH0, hTH1⟩, ⟨hTL0, hTL1⟩, -, -, -, hIC1, -, -⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
  have hFL : 0 < P.FL := by linarith
  have hFH : 0 < P.FH := by linarith
  have hδI : 0 < P.δI := by linarith
  have hD : 0 < P.δI * P.FLH - (1 + τ) * P.δU * P.FL := by
    nlinarith [mul_le_mul_of_nonneg_right hτFB hFL.le, mul_lt_mul_of_pos_left h5 hδI]
  have hN : 0 ≤ (P.δI - (1 + τ) * P.δU) * P.FH := mul_nonneg (by linarith) hFH.le
  have htD : Tbar P τ * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL) =
      (P.δI - (1 + τ) * P.δU) * P.FH := by
    unfold Tbar; exact div_mul_cancel₀ _ hD.ne'
  have hTLt : TL ≤ Tbar P τ := by
    have := mul_le_mul_of_nonneg_left hTH1 hN
    have h1' : TL * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL) ≤
        Tbar P τ * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL) := by
      rw [htD]; nlinarith
    exact le_of_mul_le_mul_right h1' hD
  have e : sepWelfare P τ TH TL = Wstar P - P.β * (P.δI - P.δU) * (1 - TH) * P.FH -
      (1 - P.β) * (P.δI - P.δU) * (1 - TL) * P.FL := by
    unfold sepWelfare welfare Wstar; ring
  rw [e]
  unfold WS
  have a1 := mul_nonneg (mul_nonneg (mul_nonneg h11.le (sub_nonneg.2 h9.le))
    (sub_nonneg.2 hTH1)) hFH.le
  have a2 := mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 h12.le) (sub_nonneg.2 h9.le))
    (sub_nonneg.2 hTLt)) hFL.le
  nlinarith

lemma sepWelfare_tbar (P : Firm) (τ : ℝ) : sepWelfare P τ 1 (Tbar P τ) = WS P τ := by
  unfold sepWelfare welfare WS Wstar; ring

/-- The Pareto-optimal pooling equilibrium `T_P = 1` exists for `0 ≤ τ ≤ τ*`. -/
lemma pool_one (P : Firm) (hS : Standing P) (h0 : Coexist P 0) (τ : ℝ) (hτ0 : 0 ≤ τ)
    (hc : (1 + τ) * P.δU * Fbar P ≤ P.δI * P.FbL) : IsPoolingEq P τ 1 := by
  have hfb := fbar_bounds P hS
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
  have hFL : 0 < P.FL := by linarith
  have hFH : 0 < P.FH := by linarith
  have hδI : 0 < P.δI := by linarith
  have hk : 0 ≤ (1 + τ) * P.δU := by positivity
  have hR1 : 0 ≤ P.δI * P.FbH - (1 + τ) * P.δU * Fbar P := by
    nlinarith [mul_le_mul_of_nonneg_left h8.le hδI.le]
  have hR2 : 0 ≤ P.δI * P.FbL - (1 + τ) * P.δU * Fbar P := by linarith
  refine ⟨⟨zero_lt_one, le_rfl⟩, by linarith, by linarith, ?_⟩
  intro T' hT' _
  constructor
  · have c := h0.2.1
    have hL : P.δI * P.FH - (1 + τ) * P.δU * P.FH ≤ P.δI * P.FbH - (1 + τ) * P.δU * Fbar P := by
      have := mul_nonneg (mul_nonneg hτ0 h10.le) (show 0 ≤ P.FH - Fbar P by linarith)
      nlinarith
    have := lin_aux _ _ T' hL hR1 hT'.1 hT'.2
    linarith
  · have hL : P.δI * P.FHL - (1 + τ) * P.δU * P.FH ≤ P.δI * P.FbL - (1 + τ) * P.δU * Fbar P := by
      have := mul_le_mul_of_nonneg_left h4 hδI.le
      have := mul_le_mul_of_nonneg_left (show Fbar P ≤ P.FH by linarith) hk
      nlinarith
    have := lin_aux _ _ T' hL hR2 hT'.1 hT'.2
    linarith

end TFTT6Aux

open TFTT6Aux in
theorem solution (P : Firm) (VH VL v : ℝ)
    (hS : Standing P) (h23 : Spec23 P VH VL v) (hv : 0 < v)
    (h0 : Coexist P 0) (hτ : tauStar P < tau0 P v) :
    0 < tauStar P ∧ tauStar P < tauFB P ∧
    poolWelfare P 0 1 < WS P 0 ∧
    (∀ τ, 0 ≤ τ → τ ≤ tauStar P → IsPoolingEq P τ 1) ∧
    (∀ τ, tauStar P < τ → ∀ TP, ¬ IsPoolingEq P τ TP) ∧
    (∀ τ, tauStar P < τ → τ ≤ tauFB P →
      IsGreatest {w | ∃ TH TL, IsSeparatingEq P τ TH TL ∧ w = sepWelfare P τ TH TL} (WS P τ)) ∧
    StrictAntiOn (WS P) (Set.Icc 0 (tauFB P)) ∧
    poolWelfare P 0 1 < WS P (tauStar P) ∧
    (∀ τ, tauStar P < τ → τ ≤ tauFB P →
      (poolWelfare P τ 1 < WS P τ ↔ τ < tau0 P v)) ∧
    (∀ τ, tauFB P < τ →
      (∀ TH TL, ¬ IsSeparatingEq P τ TH TL) ∧ ∀ TP, ¬ IsPoolingEq P τ TP) := by
  obtain ⟨tsPos, tsIff, tsLt⟩ := tauStar_step P hS h0
  have T0 := (tau0_step P VH VL v hS h23 hv).1
  have TD := (tbar_deriv P hS).2
  have hpool : ∀ τ, poolWelfare P τ 1 = Wstar P - P.δI * v := fun τ =>
    (welfare_24_25 P τ 0 VH VL v).2.2.2 h23
  have hcoef : 0 < (1 - P.β) * (P.δI - P.δU) * P.FL := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
    have : 0 < P.FL := by linarith
    have : 0 < 1 - P.β := by linarith
    have : 0 < P.δI - P.δU := by linarith
    positivity
  -- item 6
  have hanti : StrictAntiOn (WS P) (Set.Icc 0 (tauFB P)) := by
    intro x hx y hy hxy
    have := TD hx hy hxy
    unfold WS
    nlinarith [mul_pos hcoef (sub_pos.2 this)]
  have hτS : tauStar P ∈ Set.Icc 0 (tauFB P) := ⟨tsPos.le, tsLt.le⟩
  have h0m : (0 : ℝ) ∈ Set.Icc 0 (tauFB P) := ⟨le_rfl, by linarith⟩
  -- item 7
  have h7 : poolWelfare P 0 1 < WS P (tauStar P) := by
    rw [hpool 0, ← hpool (tauStar P)]
    exact (T0 _ hτS).2 hτ
  -- item 4
  have h4 : ∀ τ, tauStar P < τ → ∀ TP, ¬ IsPoolingEq P τ TP := by
    intro τ hτ' TP hTP
    have := (tsIff τ (by linarith)).1 ⟨TP, hTP⟩
    linarith
  refine ⟨tsPos, tsLt, lt_trans h7 (hanti h0m hτS tsPos), ?_, h4, ?_, hanti, h7, ?_, ?_⟩
  · -- item 3
    intro τ hτ0 hτS'
    apply pool_one P hS h0 τ hτ0
    have := (tauStar_lt_iff P hS τ).not.1 (not_lt.2 hτS')
    linarith
  · -- item 5
    intro τ hτ1 hτ2
    have hk := (le_tauFB_iff P hS τ).1 hτ2
    refine ⟨⟨1, Tbar P τ, sepEq_tbar P hS h0 τ (by linarith) hk, (sepWelfare_tbar P τ).symm⟩, ?_⟩
    rintro w ⟨TH, TL, hE, rfl⟩
    exact sep_bound P hS τ hk TH TL hE
  · -- item 8
    intro τ hτ1 hτ2
    exact T0 τ ⟨by linarith, hτ2⟩
  · -- item 9
    intro τ hτ1
    refine ⟨?_, h4 τ (by linarith)⟩
    intro TH TL hE
    have hk := (tauFB_lt_iff P hS τ).1 hτ1
    obtain ⟨⟨hTH0, hTH1⟩, ⟨hTL0, hTL1⟩, hne, hpH, hpL, -, -, -⟩ := hE
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
    have hFL : 0 < P.FL := by linarith
    have hFH : 0 < P.FH := by linarith
    have a1 : TH ≤ 0 := by
      by_contra hc
      rw [not_le] at hc
      nlinarith [mul_pos (mul_pos hc hFH) (sub_pos.2 hk)]
    have a2 : TL ≤ 0 := by
      by_contra hc
      rw [not_le] at hc
      nlinarith [mul_pos (mul_pos hc hFL) (sub_pos.2 hk)]
    exact hne (by linarith)
