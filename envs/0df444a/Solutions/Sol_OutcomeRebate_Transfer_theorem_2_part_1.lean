-- Prove2me | solution 1 for OutcomeRebate.Transfer.theorem_2_part_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:41:15.627616+00:00
-- url     : https://prove2.me/submissions/c917f4ad-67e9-488d-b050-c38214121e7e

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Theorems.Thm_OutcomeRebate_Transfer_closed_forms_outcome

namespace OutcomeRebate.Transfer
open MeasureTheory

lemma obp_k_pos (P : Params) (hS : P.Standing) : 0 < P.lam * (1 - P.q) / P.q := by
  obtain ⟨_, _, _, _, _, hq0, hq1, _, _, hlam, _⟩ := hS
  apply div_pos _ hq0
  apply mul_pos (by linarith) (by linarith)

lemma obp_z_eq (P : Params) : P.z = 1 + (P.lam * (1 - P.q) / P.q) ^ (1 / P.α) := rfl

lemma obp_z_ge_one (P : Params) (hS : P.Standing) : 1 ≤ P.z := by
  rw [obp_z_eq]
  have := Real.rpow_nonneg (obp_k_pos P hS).le (1 / P.α)
  linarith

alias obp_closed_forms_outcome := closed_forms_outcome

lemma obp_A1 (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) :
    P.β * P.c < P.vbar * P.q ∧ P.β * P.c * P.z < P.vbar := by
  have hz1 := obp_z_ge_one P hS
  obtain ⟨_, hv, _, _, _, _, _, _, _, _, _⟩ := hS
  unfold Assumption1 at hA1
  rw [lt_min_iff] at hA1
  obtain ⟨h1, h2⟩ := hA1
  rw [div_lt_iff₀ hv] at h1
  rw [div_lt_iff₀ hv, div_mul_eq_mul_div, one_mul, lt_div_iff₀ (by linarith)] at h2
  constructor <;> nlinarith

lemma obp_share_cases_O (P : Params) (p : ℝ) : shareO P p = P.β ∨ shareO P p = 1 := by
  unfold shareO; split_ifs <;> simp

lemma obp_firmO (P : Params) (hS : P.Standing) (bb p : ℝ) (hbb : bb = P.β ∨ bb = 1)
    (hp : 0 ≤ p) :
    firmProfitO P bb p = (P.q * p - P.c) * (P.n / P.vbar * max (P.vbar - bb * p) 0) := by
  rw [firmProfitO, (obp_closed_forms_outcome P hS bb p hbb hp).1]

lemma obp_pTilde_pos (P : Params) (hS : P.Standing) : 0 < pTilde P := by
  obtain ⟨_, hv, hc, hβ, _, hq, _, _, _, _, _⟩ := hS
  unfold pTilde; positivity

/-- Bound on outcome-based profit. -/
theorem obp_profitO_bound (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (bb p : ℝ)
    (hbb : bb = P.β ∨ bb = 1) (hp : 0 ≤ p) :
    firmProfitO P bb p ≤ firmProfitO P P.β (pTilde P) ∧
      (firmProfitO P P.β (pTilde P) ≤ firmProfitO P bb p → p = pTilde P) := by
  have hS' := hS
  obtain ⟨hn, hv, hc, hβ, hβh, hq0, hq1, _, _, _, _⟩ := hS'
  obtain ⟨hA, _⟩ := obp_A1 P hS hA1
  have hbbβ : P.β ≤ bb := by rcases hbb with h | h <;> rw [h]; linarith
  rw [obp_firmO P hS bb p hbb hp, obp_firmO P hS P.β _ (Or.inl rfl) (obp_pTilde_pos P hS).le]
  set w := P.vbar / P.β with hwdef
  set C := P.c / P.q with hCdef
  have hw : P.vbar = P.β * w := by rw [hwdef]; field_simp
  have hC : P.c = P.q * C := by rw [hCdef]; field_simp
  have hpt : pTilde P = C / 2 + w / 2 := by
    unfold pTilde; rw [hwdef, hCdef]; field_simp
  set N := P.n / P.vbar
  have hN : 0 < N := div_pos hn hv
  have hbq : 0 < P.β * P.q := by positivity
  have hwc : C < w := by
    rw [hw, hC] at hA; nlinarith
  rw [hpt]
  have hmax : max (P.vbar - P.β * (C / 2 + w / 2)) 0 = P.β * (w - C) / 2 := by
    rw [max_eq_left] <;> rw [hw] <;> nlinarith
  rw [hmax]
  have hG : 0 < (P.q * (C / 2 + w / 2) - P.c) * (N * (P.β * (w - C) / 2)) := by
    rw [hC]
    apply mul_pos (by nlinarith); apply mul_pos hN; nlinarith
  set G := (P.q * (C / 2 + w / 2) - P.c) * (N * (P.β * (w - C) / 2))
  have hD0 : 0 ≤ max (P.vbar - bb * p) 0 := le_max_right _ _
  have main : (P.q * p - P.c) * (N * max (P.vbar - bb * p) 0) ≤
      G - N * (P.β * P.q) * (p - (C / 2 + w / 2)) ^ 2 ∨
      (P.q * p - P.c) * (N * max (P.vbar - bb * p) 0) ≤ 0 := by
    rcases le_or_gt (P.q * p) P.c with hpc | hpc
    · right
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (mul_nonneg hN.le hD0)
    · rcases le_or_gt (P.vbar - P.β * p) 0 with hd | hd
      · right
        have : max (P.vbar - bb * p) 0 = 0 := by
          apply max_eq_right
          have : P.β * p ≤ bb * p := mul_le_mul_of_nonneg_right hbbβ hp
          linarith
        rw [this]; simp
      · left
        have hle : max (P.vbar - bb * p) 0 ≤ P.vbar - P.β * p := by
          apply max_le _ hd.le
          have : P.β * p ≤ bb * p := mul_le_mul_of_nonneg_right hbbβ hp
          linarith
        have e : (P.q * p - P.c) * (N * (P.vbar - P.β * p)) =
            G - N * (P.β * P.q) * (p - (C / 2 + w / 2)) ^ 2 := by
          simp only [G]; rw [hw, hC]; ring
        rw [← e]
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact mul_le_mul_of_nonneg_left hle hN.le
  have hsq : 0 ≤ N * (P.β * P.q) * (p - (C / 2 + w / 2)) ^ 2 := by positivity
  constructor
  · rcases main with h | h <;> linarith
  · intro hge
    rcases main with h | h
    · have : N * (P.β * P.q) * (p - (C / 2 + w / 2)) ^ 2 ≤ 0 := by linarith
      have h2 : (p - (C / 2 + w / 2)) ^ 2 ≤ 0 := by
        by_contra hc'
        push Not at hc'
        have := mul_pos (mul_pos hN hbq) hc'
        linarith
      have : p - (C / 2 + w / 2) = 0 := by nlinarith
      linarith
    · linarith

theorem obp_eqO_of_covers (P : Params) (hS : P.Standing) (hA1 : Assumption1 P)
    (hcov : coversO P (pTilde P)) :
    IsEqPriceO P (pTilde P) ∧ ∀ p : ℝ, IsEqPriceO P p → p = pTilde P := by
  have hps := (obp_pTilde_pos P hS).le
  have hsh : shareO P (pTilde P) = P.β := by unfold shareO; rw [if_pos hcov]
  refine ⟨⟨hps, fun p' hp' => ?_⟩, fun p hp => ?_⟩
  · rw [realizedProfitO, realizedProfitO, hsh]
    exact (obp_profitO_bound P hS hA1 _ p' (obp_share_cases_O P p') hp').1
  · have h := hp.2 (pTilde P) hps
    rw [realizedProfitO, realizedProfitO, hsh] at h
    exact (obp_profitO_bound P hS hA1 _ p (obp_share_cases_O P p) hp.1).2 h

theorem obp_coversO_pTilde (P : Params) (hS : P.Standing) (hA1 : Assumption1 P)
    (h : pTilde P * (1 - P.β / 2) - P.vbar / 2 ≤ P.vp) :
    coversO P (pTilde P) := by
  have hS' := hS
  obtain ⟨hn, hv, hc, hβ, hβh, hq0, hq1, _, _, _, _⟩ := hS'
  have hps := (obp_pTilde_pos P hS).le
  unfold coversO
  rw [(obp_closed_forms_outcome P hS 1 _ (Or.inr rfl) hps).2,
    (obp_closed_forms_outcome P hS P.β _ (Or.inl rfl) hps).2]
  have h1 : max (P.vbar - 1 * pTilde P) 0 = 0 := by
    apply max_eq_right
    have : P.vbar ≤ P.vbar / (2 * P.β) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    have : 0 < P.c / (2 * P.q) := by positivity
    unfold pTilde; linarith
  rw [h1]
  simp only [mul_zero, zero_mul]
  apply mul_nonneg (mul_nonneg (by positivity) (le_max_right _ _))
  linarith

theorem obp_theorem_2_part_1 (P : Params) (hS : P.Standing) (hA1 : Assumption1 P)
    (h : pTilde P * (1 - P.β / 2) - P.vbar / 2 ≤ P.vp) :
    IsEqPriceO P (pTilde P) ∧ coversO P (pTilde P) ∧
      ∀ p : ℝ, IsEqPriceO P p → p = pTilde P := by
  have hcO : coversO P (pTilde P) := obp_coversO_pTilde P hS hA1 h
  obtain ⟨hO1, hO2⟩ := obp_eqO_of_covers P hS hA1 hcO
  exact ⟨hO1, hcO, hO2⟩


end OutcomeRebate.Transfer

open OutcomeRebate.Transfer

theorem solution (P : Params) (hS : P.Standing) (hA1 : Assumption1 P)
    (h : pTilde P * (1 - P.β / 2) - P.vbar / 2 ≤ P.vp) :
    IsEqPriceO P (pTilde P) ∧ coversO P (pTilde P) ∧
      ∀ p : ℝ, IsEqPriceO P p → p = pTilde P :=
  obp_theorem_2_part_1 P hS hA1 h
