-- Prove2me | solution 1 for OutcomeRebate.Transfer.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:38:23.659364+00:00
-- url     : https://prove2.me/submissions/c1415af7-8e8d-40d0-8fd0-4b37199bc821

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Theorems.Thm_OutcomeRebate_Transfer_proposition_3_part_3
import Theorems.Thm_OutcomeRebate_Transfer_proposition_3_part_6
import Theorems.Thm_OutcomeRebate_Transfer_joint_surplus_identity
import Theorems.Thm_OutcomeRebate_Transfer_joint_surplus_bracket_pos
import Theorems.Thm_OutcomeRebate_Transfer_assumption_2_equilibrium

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

alias obp_assumption_2_equilibrium := assumption_2_equilibrium

alias obp_proposition_3_part_3 := proposition_3_part_3

alias obp_proposition_3_part_6 := proposition_3_part_6

alias obp_joint_surplus_identity := joint_surplus_identity

alias obp_joint_surplus_bracket_pos := joint_surplus_bracket_pos

lemma obp_K_pos (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) :
    0 < P.n / (4 * P.vbar * P.β) * (P.vbar ^ 2 / P.z - P.c ^ 2 * P.β ^ 2 / P.q) := by
  have hS' := hS
  obtain ⟨hn, hv, hc, hβ, hβh, hq0, hqlt, hα0, hα1, hlam, hvp⟩ := hS'
  have hz1 := obp_z_ge_one P hS
  obtain ⟨hA, hA'⟩ := obp_A1 P hS hA1
  apply mul_pos (by positivity)
  rw [sub_pos, div_lt_div_iff₀ hq0 (by linarith)]
  have h1 : 0 < P.β * P.c := by positivity
  nlinarith [mul_lt_mul'' hA hA' h1.le (by positivity)]

lemma obp_realized (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (q1 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β) (hA2 : Assumption2 P q1)
    (pU pO : ℝ) (hU : IsEqPriceU P pU) (hO : IsEqPriceO P pO) :
    realizedProfitU P pU = firmProfitU P P.β (pStar P) ∧
    realizedProfitO P pO = firmProfitO P P.β (pTilde P) ∧
    realizedObjU P pU = payerObjU P P.β (pStar P) ∧
    realizedObjO P pO = payerObjO P P.β (pTilde P) := by
  obtain ⟨⟨_, hcU, hU2⟩, ⟨_, hcO, hO2⟩⟩ := obp_assumption_2_equilibrium P hS hA1 q1 hq1 hA2
  have e1 := hU2 pU hU
  have e2 := hO2 pO hO
  subst e1 e2
  have hsU : shareU P (pStar P) = P.β := by unfold shareU; rw [if_pos hcU]
  have hsO : shareO P (pTilde P) = P.β := by unfold shareO; rw [if_pos hcO]
  simp only [realizedProfitU, realizedProfitO, realizedObjU, realizedObjO, hsU, hsO, and_self]

lemma obp_mul_neg_iff {K x : ℝ} (hK : 0 < K) : K * x < 0 ↔ x < 0 := by
  constructor
  · intro h; by_contra hc; push Not at hc; nlinarith [mul_nonneg hK.le hc]
  · intro h; exact mul_neg_of_pos_of_neg hK h

theorem obp_proposition_4 (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (q1 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β) (hA2 : Assumption2 P q1)
    (pU pO : ℝ) (hU : IsEqPriceU P pU) (hO : IsEqPriceO P pO) :
    let dPi := realizedProfitO P pO - realizedProfitU P pU
    let dW := realizedObjO P pO - realizedObjU P pU
    (Mprime P < P.vp → ((0 < dPi ↔ 0 < dW) ∧ (dPi < 0 ↔ dW < 0))) ∧
    (P.vp < Mprime P →
      ((∃ τ : ℝ, realizedProfitU P pU < realizedProfitO P pO - τ ∧
          realizedObjU P pU < realizedObjO P pO + τ) ↔ P.q < q0 P.α P.lam)) ∧
    (P.vp < Mprime P → P.q < q0 P.α P.lam → 0 < -dW ∧ -dW < dPi) := by
  intro dPi dW
  have hS' := hS
  obtain ⟨hn, hv, hc, hβ, hβh, hq0, hqlt, hα0, hα1, hlam, hvp⟩ := hS'
  obtain ⟨hPi, hPiiff⟩ := obp_proposition_3_part_3 P hS hA1 q1 hq1 hA2 pU pO hU hO
  obtain ⟨hW, _⟩ := obp_proposition_3_part_6 P hS hA1 q1 hq1 hA2 pU pO hU hO
  obtain ⟨r1, r2, r3, r4⟩ := obp_realized P hS hA1 q1 hq1 hA2 pU pO hU hO
  have hJ := obp_joint_surplus_identity P hS hA1
  have hBr := obp_joint_surplus_bracket_pos P hS hA1 q1 hq1 hA2
  have hK := obp_K_pos P hS hA1
  have hKW : 0 < P.n * P.β * P.c / (2 * P.vbar) := by positivity
  have hKJ : 0 < P.n * P.β * P.c / (4 * P.vbar) := by positivity
  set K := P.n / (4 * P.vbar * P.β) * (P.vbar ^ 2 / P.z - P.c ^ 2 * P.β ^ 2 / P.q)
  set B := 2 * P.vp + P.vbar - 2 * P.c / P.q + P.β * P.c / (2 * P.q) + P.β * P.c * P.z / 2
  have hdPi : dPi = K * (P.q * P.z - 1) := by
    simp only [dPi, hPi, K]; ring
  have hdW : dW = P.n * P.β * P.c / (2 * P.vbar) * (P.q * P.z - 1) * (P.vp - Mprime P) := hW
  have hsum : dPi + dW = P.n * P.β * P.c / (4 * P.vbar) * (P.q * P.z - 1) * B := by
    simp only [dPi, dW, r1, r2, r3, r4]; rw [← hJ]; ring
  -- `q < q₀ ↔ 0 < qz - 1`
  have hq0iff : P.q < q0 P.α P.lam ↔ 0 < P.q * P.z - 1 := by
    rw [← hPiiff, ← sub_pos]
    change 0 < dPi ↔ _
    rw [hdPi, mul_pos_iff_of_pos_left hK]
  refine ⟨fun hM => ?_, fun hM => ?_, fun hM hq => ?_⟩
  · have hM' : 0 < P.vp - Mprime P := by linarith
    rw [hdPi, hdW]
    constructor
    · rw [mul_pos_iff_of_pos_left hK, mul_assoc, mul_pos_iff_of_pos_left hKW,
        mul_pos_iff_of_pos_right hM']
    · rw [obp_mul_neg_iff hK, mul_assoc, obp_mul_neg_iff hKW]
      constructor
      · intro h; exact mul_neg_of_neg_of_pos h hM'
      · intro h; by_contra hc; push Not at hc; nlinarith [mul_nonneg hc hM'.le]
  · rw [hq0iff]
    constructor
    · rintro ⟨τ, h1, h2⟩
      have : 0 < dPi + dW := by simp only [dPi, dW]; linarith
      rw [hsum] at this
      by_contra hc
      push Not at hc
      have h3 := mul_nonpos_of_nonneg_of_nonpos hKJ.le hc
      have := mul_nonpos_of_nonpos_of_nonneg h3 hBr.le
      linarith
    · intro h
      have : 0 < dPi + dW := by
        rw [hsum]; exact mul_pos (mul_pos hKJ h) hBr
      refine ⟨(dPi - dW) / 2, ?_, ?_⟩
      · simp only [dPi, dW] at this ⊢; linarith
      · simp only [dPi, dW] at this ⊢; linarith
  · rw [hq0iff] at hq
    have hM' : P.vp - Mprime P < 0 := by linarith
    constructor
    · rw [hdW]
      have : P.n * P.β * P.c / (2 * P.vbar) * (P.q * P.z - 1) * (P.vp - Mprime P) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hKW hq) hM'
      linarith
    · have : 0 < dPi + dW := by
        rw [hsum]; exact mul_pos (mul_pos hKJ hq) hBr
      linarith


end OutcomeRebate.Transfer

open OutcomeRebate.Transfer

theorem solution (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (q1 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β) (hA2 : Assumption2 P q1)
    (pU pO : ℝ) (hU : IsEqPriceU P pU) (hO : IsEqPriceO P pO) :
    let dPi := realizedProfitO P pO - realizedProfitU P pU
    let dW := realizedObjO P pO - realizedObjU P pU
    (Mprime P < P.vp → ((0 < dPi ↔ 0 < dW) ∧ (dPi < 0 ↔ dW < 0))) ∧
    (P.vp < Mprime P →
      ((∃ τ : ℝ, realizedProfitU P pU < realizedProfitO P pO - τ ∧
          realizedObjU P pU < realizedObjO P pO + τ) ↔ P.q < q0 P.α P.lam)) ∧
    (P.vp < Mprime P → P.q < q0 P.α P.lam → 0 < -dW ∧ -dW < dPi) :=
  obp_proposition_4 P hS hA1 q1 hq1 hA2 pU pO hU hO
