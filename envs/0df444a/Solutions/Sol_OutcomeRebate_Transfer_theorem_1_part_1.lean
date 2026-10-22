-- Prove2me | solution 1 for OutcomeRebate.Transfer.theorem_1_part_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:41:13.889028+00:00
-- url     : https://prove2.me/submissions/144c146c-2bcc-4015-b079-fd56994dca5c

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Theorems.Thm_OutcomeRebate_Transfer_closed_forms_uniform
import Theorems.Thm_OutcomeRebate_Transfer_zq_monotone

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

alias obp_closed_forms_uniform := closed_forms_uniform

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

lemma obp_share_cases_U (P : Params) (p : ℝ) : shareU P p = P.β ∨ shareU P p = 1 := by
  unfold shareU; split_ifs <;> simp

lemma obp_firmU (P : Params) (hS : P.Standing) (bb p : ℝ) (hbb : bb = P.β ∨ bb = 1)
    (hp : 0 ≤ p) :
    firmProfitU P bb p = (p - P.c) * (P.n / P.vbar * max (P.vbar - bb * p * P.z) 0) := by
  rw [firmProfitU, (obp_closed_forms_uniform P hS bb p hbb hp).1]

lemma obp_pStar_pos (P : Params) (hS : P.Standing) : 0 < pStar P := by
  have hz1 := obp_z_ge_one P hS
  obtain ⟨_, hv, hc, hβ, _, _, _, _, _, _, _⟩ := hS
  unfold pStar; positivity

lemma obp_pStar_w (P : Params) (hS : P.Standing) :
    pStar P = P.c / 2 + P.vbar / (P.β * P.z) / 2 ∧
      P.vbar = P.β * P.z * (P.vbar / (P.β * P.z)) := by
  have hz1 := obp_z_ge_one P hS
  obtain ⟨_, hv, hc, hβ, _, _, _, _, _, _, _⟩ := hS
  have : P.β * P.z ≠ 0 := by positivity
  constructor
  · unfold pStar; field_simp
  · field_simp

/-- Bound on uniform-pricing profit. -/
theorem obp_profitU_bound (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (bb p : ℝ)
    (hbb : bb = P.β ∨ bb = 1) (hp : 0 ≤ p) :
    firmProfitU P bb p ≤ firmProfitU P P.β (pStar P) ∧
      (firmProfitU P P.β (pStar P) ≤ firmProfitU P bb p → p = pStar P) := by
  have hS' := hS
  obtain ⟨hn, hv, hc, hβ, hβh, hq0, hq1, _, _, _, _⟩ := hS'
  have hz1 := obp_z_ge_one P hS
  obtain ⟨_, hA⟩ := obp_A1 P hS hA1
  have hbbβ : P.β ≤ bb := by rcases hbb with h | h <;> rw [h]; linarith
  rw [obp_firmU P hS bb p hbb hp, obp_firmU P hS P.β _ (Or.inl rfl) (obp_pStar_pos P hS).le]
  obtain ⟨hps, hw⟩ := obp_pStar_w P hS
  set w := P.vbar / (P.β * P.z)
  set N := P.n / P.vbar
  have hN : 0 < N := div_pos hn hv
  have hbz : 0 < P.β * P.z := by positivity
  have hwc : P.c < w := by
    rw [hw] at hA; nlinarith
  rw [hps]
  have hmax : max (P.vbar - P.β * (P.c / 2 + w / 2) * P.z) 0 =
      P.β * P.z * (w - P.c) / 2 := by
    rw [max_eq_left] <;> rw [hw] <;> nlinarith
  rw [hmax]
  have hG : 0 < (P.c / 2 + w / 2 - P.c) * (N * (P.β * P.z * (w - P.c) / 2)) := by
    apply mul_pos (by linarith); apply mul_pos hN; nlinarith
  set G := (P.c / 2 + w / 2 - P.c) * (N * (P.β * P.z * (w - P.c) / 2))
  have hD0 : 0 ≤ max (P.vbar - bb * p * P.z) 0 := le_max_right _ _
  -- the main estimate
  have main : (p - P.c) * (N * max (P.vbar - bb * p * P.z) 0) ≤
      G - N * (P.β * P.z) * (p - (P.c / 2 + w / 2)) ^ 2 ∨
      (p - P.c) * (N * max (P.vbar - bb * p * P.z) 0) ≤ 0 := by
    rcases le_or_gt p P.c with hpc | hpc
    · right
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (mul_nonneg hN.le hD0)
    · rcases le_or_gt (P.vbar - P.β * p * P.z) 0 with hd | hd
      · right
        have : max (P.vbar - bb * p * P.z) 0 = 0 := by
          apply max_eq_right
          have : P.β * p * P.z ≤ bb * p * P.z := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            exact mul_le_mul_of_nonneg_right hbbβ hp
          linarith
        rw [this]; simp
      · left
        have hle : max (P.vbar - bb * p * P.z) 0 ≤ P.vbar - P.β * p * P.z := by
          apply max_le _ hd.le
          have : P.β * p * P.z ≤ bb * p * P.z := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            exact mul_le_mul_of_nonneg_right hbbβ hp
          linarith
        have e : (p - P.c) * (N * (P.vbar - P.β * p * P.z)) =
            G - N * (P.β * P.z) * (p - (P.c / 2 + w / 2)) ^ 2 := by
          simp only [G]; rw [hw]; ring
        rw [← e]
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact mul_le_mul_of_nonneg_left hle hN.le
  have hsq : 0 ≤ N * (P.β * P.z) * (p - (P.c / 2 + w / 2)) ^ 2 := by positivity
  constructor
  · rcases main with h | h <;> linarith
  · intro hge
    rcases main with h | h
    · have : N * (P.β * P.z) * (p - (P.c / 2 + w / 2)) ^ 2 ≤ 0 := by linarith
      have h2 : (p - (P.c / 2 + w / 2)) ^ 2 ≤ 0 := by
        by_contra hc'
        push Not at hc'
        have := mul_pos (mul_pos hN hbz) hc'
        linarith
      have : p - (P.c / 2 + w / 2) = 0 := by nlinarith
      linarith
    · linarith

theorem obp_eqU_of_covers (P : Params) (hS : P.Standing) (hA1 : Assumption1 P)
    (hcov : coversU P (pStar P)) :
    IsEqPriceU P (pStar P) ∧ ∀ p : ℝ, IsEqPriceU P p → p = pStar P := by
  have hps := (obp_pStar_pos P hS).le
  have hsh : shareU P (pStar P) = P.β := by unfold shareU; rw [if_pos hcov]
  refine ⟨⟨hps, fun p' hp' => ?_⟩, fun p hp => ?_⟩
  · rw [realizedProfitU, realizedProfitU, hsh]
    exact (obp_profitU_bound P hS hA1 _ p' (obp_share_cases_U P p') hp').1
  · have h := hp.2 (pStar P) hps
    rw [realizedProfitU, realizedProfitU, hsh] at h
    exact (obp_profitU_bound P hS hA1 _ p (obp_share_cases_U P p) hp.1).2 h

theorem obp_coversU_pStar (P : Params) (hS : P.Standing) (hA1 : Assumption1 P)
    (h : 0 ≤ P.q * P.vp - pStar P + P.q / 2 * (P.vbar + P.β * pStar P * P.z)) :
    coversU P (pStar P) := by
  have hS' := hS
  obtain ⟨hn, hv, hc, hβ, hβh, hq0, hq1, _, _, _, _⟩ := hS'
  have hz1 := obp_z_ge_one P hS
  obtain ⟨_, hA⟩ := obp_A1 P hS hA1
  have hps := (obp_pStar_pos P hS).le
  unfold coversU
  rw [(obp_closed_forms_uniform P hS 1 _ (Or.inr rfl) hps).2,
    (obp_closed_forms_uniform P hS P.β _ (Or.inl rfl) hps).2]
  obtain ⟨hpsw, hw⟩ := obp_pStar_w P hS
  have hbz : 0 < P.β * P.z := by positivity
  have h1 : max (P.vbar - 1 * pStar P * P.z) 0 = 0 := by
    apply max_eq_right
    rw [hpsw]
    have e : P.vbar / (P.β * P.z) / 2 * P.z = P.vbar / (2 * P.β) := by
      field_simp
    have : P.vbar ≤ P.vbar / (2 * P.β) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    nlinarith
  rw [h1]
  simp only [mul_zero, zero_mul]
  apply mul_nonneg (mul_nonneg (div_pos hn hv).le (le_max_right _ _)) h

/-- If `zq ≥ 1/β`, the payer covers at `p∗` whatever `v′ ≥ 0` is. -/
theorem obp_bracket_of_zq (P : Params) (hS : P.Standing) (hA1 : Assumption1 P)
    (hzq : 1 / P.β ≤ P.z * P.q) :
    0 ≤ P.q * P.vp - pStar P + P.q / 2 * (P.vbar + P.β * pStar P * P.z) := by
  have hS' := hS
  obtain ⟨hn, hv, hc, hβ, hβh, hq0, hq1, _, _, _, hvp⟩ := hS'
  have hz1 := obp_z_ge_one P hS
  obtain ⟨_, hA⟩ := obp_A1 P hS hA1
  obtain ⟨hpsw, hw⟩ := obp_pStar_w P hS
  set w := P.vbar / (P.β * P.z)
  have hs : 1 ≤ P.q * P.β * P.z := by
    rw [div_le_iff₀ hβ] at hzq; linarith
  rw [hpsw]
  have hwc : P.c < w := by rw [hw] at hA; nlinarith [mul_pos hβ (by linarith : (0:ℝ) < P.z)]
  -- q v̄ = s w where s = qβz
  have e : P.q * P.vbar = P.q * P.β * P.z * w := by rw [hw]; ring
  have : 0 ≤ P.q * P.vp := mul_nonneg hq0.le hvp
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ P.q * P.β * P.z - 1) (by linarith : (0:ℝ) ≤ w - P.c)]

theorem obp_theorem_1_part_1 (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (qbar1 : ℝ)
    (hqbar1 : 0 < qbar1 ∧ qbar1 < 1 ∧ zOf P.α P.lam qbar1 * qbar1 = 1 / P.β)
    (h : P.q ≤ qbar1 ∨
      (qbar1 < P.q ∧ pStar P * (1 / P.q - P.z * P.β / 2) - P.vbar / 2 ≤ P.vp)) :
    IsEqPriceU P (pStar P) ∧ coversU P (pStar P) ∧
      ∀ p : ℝ, IsEqPriceU P p → p = pStar P := by
  have hS' := hS
  obtain ⟨hn, hv, hc, hβ, hβh, hq0, hqlt, hα0, hα1, hlam, hvp⟩ := hS'
  have hcU : coversU P (pStar P) := by
    apply obp_coversU_pStar P hS hA1
    rcases h with h | ⟨_, h⟩
    · apply obp_bracket_of_zq P hS hA1
      have hk : 1 < 1 / P.β := by rw [lt_div_iff₀ hβ]; linarith
      exact ((zq_monotone P.α P.lam ⟨hα0, hα1⟩ hlam).2.2.2 (1 / P.β) qbar1 hk hqbar1.1
        hqbar1.2.1 hqbar1.2.2 P.q hq0 hqlt).mpr h
    · have hm := mul_le_mul_of_nonneg_left h hq0.le
      have e : P.q * (pStar P * (1 / P.q - P.z * P.β / 2) - P.vbar / 2) =
          pStar P - P.q * P.z * P.β * pStar P / 2 - P.q * P.vbar / 2 := by
        field_simp
      rw [e] at hm
      nlinarith
  obtain ⟨hU1, hU2⟩ := obp_eqU_of_covers P hS hA1 hcU
  exact ⟨hU1, hcU, hU2⟩


end OutcomeRebate.Transfer

open OutcomeRebate.Transfer

theorem solution (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (qbar1 : ℝ)
    (hqbar1 : 0 < qbar1 ∧ qbar1 < 1 ∧ zOf P.α P.lam qbar1 * qbar1 = 1 / P.β)
    (h : P.q ≤ qbar1 ∨
      (qbar1 < P.q ∧ pStar P * (1 / P.q - P.z * P.β / 2) - P.vbar / 2 ≤ P.vp)) :
    IsEqPriceU P (pStar P) ∧ coversU P (pStar P) ∧
      ∀ p : ℝ, IsEqPriceU P p → p = pStar P :=
  obp_theorem_1_part_1 P hS hA1 qbar1 hqbar1 h
