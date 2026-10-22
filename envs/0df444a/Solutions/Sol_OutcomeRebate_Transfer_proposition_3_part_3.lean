-- Prove2me | solution 1 for OutcomeRebate.Transfer.proposition_3_part_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:41:06.893587+00:00
-- url     : https://prove2.me/submissions/63cde771-6cce-472f-a456-1507d6802147

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Theorems.Thm_OutcomeRebate_Transfer_assumption_2_equilibrium
import Theorems.Thm_OutcomeRebate_Transfer_closed_forms_uniform
import Theorems.Thm_OutcomeRebate_Transfer_closed_forms_outcome
import Theorems.Thm_OutcomeRebate_Transfer_lemma_1
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

alias obp_closed_forms_uniform := closed_forms_uniform

alias obp_closed_forms_outcome := closed_forms_outcome

alias obp_assumption_2_equilibrium := assumption_2_equilibrium

lemma obp_firmU (P : Params) (hS : P.Standing) (bb p : ℝ) (hbb : bb = P.β ∨ bb = 1)
    (hp : 0 ≤ p) :
    firmProfitU P bb p = (p - P.c) * (P.n / P.vbar * max (P.vbar - bb * p * P.z) 0) := by
  rw [firmProfitU, (obp_closed_forms_uniform P hS bb p hbb hp).1]

lemma obp_firmO (P : Params) (hS : P.Standing) (bb p : ℝ) (hbb : bb = P.β ∨ bb = 1)
    (hp : 0 ≤ p) :
    firmProfitO P bb p = (P.q * p - P.c) * (P.n / P.vbar * max (P.vbar - bb * p) 0) := by
  rw [firmProfitO, (obp_closed_forms_outcome P hS bb p hbb hp).1]

lemma obp_pStar_pos (P : Params) (hS : P.Standing) : 0 < pStar P := by
  have hz1 := obp_z_ge_one P hS
  obtain ⟨_, hv, hc, hβ, _, _, _, _, _, _, _⟩ := hS
  unfold pStar; positivity

lemma obp_pTilde_pos (P : Params) (hS : P.Standing) : 0 < pTilde P := by
  obtain ⟨_, hv, hc, hβ, _, hq, _, _, _, _, _⟩ := hS
  unfold pTilde; positivity

/-- Closed-form values at `p∗` and `p̃∗` with coverage. -/
lemma obp_values (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) :
    firmProfitU P P.β (pStar P) =
        (pStar P - P.c) * (P.n / P.vbar * (P.vbar - P.β * pStar P * P.z)) ∧
    payerObjU P P.β (pStar P) = P.n / P.vbar * (P.vbar - P.β * pStar P * P.z) *
        (P.q * P.vp - pStar P + P.q / 2 * (P.vbar + P.β * pStar P * P.z)) ∧
    firmProfitO P P.β (pTilde P) =
        (P.q * pTilde P - P.c) * (P.n / P.vbar * (P.vbar - P.β * pTilde P)) ∧
    payerObjO P P.β (pTilde P) = P.n * P.q / P.vbar * (P.vbar - P.β * pTilde P) *
        (P.vp - pTilde P + (P.vbar + P.β * pTilde P) / 2) := by
  have hS' := hS
  obtain ⟨hn, hv, hc, hβ, hβh, hq0, hqlt, hα0, hα1, hlam, hvp⟩ := hS'
  have hz1 := obp_z_ge_one P hS
  obtain ⟨hA, hA'⟩ := obp_A1 P hS hA1
  have hps := (obp_pStar_pos P hS).le
  have hpt := (obp_pTilde_pos P hS).le
  have m1 : max (P.vbar - P.β * pStar P * P.z) 0 = P.vbar - P.β * pStar P * P.z := by
    apply max_eq_left
    have e : P.β * pStar P * P.z = P.β * P.c * P.z / 2 + P.vbar / 2 := by
      unfold pStar; field_simp
    rw [e]; linarith
  have m2 : max (P.vbar - P.β * pTilde P) 0 = P.vbar - P.β * pTilde P := by
    apply max_eq_left
    have e : P.β * pTilde P = P.β * P.c / P.q / 2 + P.vbar / 2 := by
      unfold pTilde; field_simp
    have : P.β * P.c / P.q < P.vbar := by rw [div_lt_iff₀ hq0]; linarith
    rw [e]; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [obp_firmU P hS _ _ (Or.inl rfl) hps, m1]
  · rw [(obp_closed_forms_uniform P hS _ _ (Or.inl rfl) hps).2, m1]
  · rw [obp_firmO P hS _ _ (Or.inl rfl) hpt, m2]
  · rw [(obp_closed_forms_outcome P hS _ _ (Or.inl rfl) hpt).2, m2]

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

lemma obp_q0_bounds (α lam : ℝ) (hα : 0 < α ∧ α < 1) (hlam : 1 ≤ lam) :
    0 < q0 α lam ∧ q0 α lam < 1 := by
  have hL : 0 < lam ^ (-(1 / (1 - α))) := Real.rpow_pos_of_pos (by linarith) _
  unfold q0
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]; linarith

lemma obp_z_pos' (α lam q : ℝ) (hlam : 1 ≤ lam) (hq : 0 < q ∧ q ≤ 1) : 0 < zOf α lam q := by
  unfold zOf
  have : 0 ≤ lam * (1 - q) / q := div_nonneg (mul_nonneg (by linarith) (by linarith)) hq.1.le
  have := Real.rpow_nonneg this (1 / α)
  linarith

theorem obp_zq_sign (α lam q : ℝ) (hα : 0 < α ∧ α < 1) (hlam : 1 ≤ lam) (hq : 0 < q ∧ q < 1) :
    (1 < zOf α lam q * q ↔ q < q0 α lam) ∧ (zOf α lam q * q < 1 ↔ q0 α lam < q) := by
  obtain ⟨hq00, hq01⟩ := obp_q0_bounds α lam hα hlam
  have hM := zq_monotone α lam hα hlam
  have hz := obp_z_pos' α lam q hlam ⟨hq.1, hq.2.le⟩
  have hz0 := obp_z_pos' α lam (q0 α lam) hlam ⟨hq00, hq01.le⟩
  have hf0 : zOf α lam (q0 α lam) * q0 α lam = 1 := by
    have := (lemma_1 α lam (q0 α lam) hα hlam ⟨hq00, hq01.le⟩).1 (Or.inl rfl)
    rw [div_eq_iff hz0.ne'] at this
    linarith
  rcases lt_trichotomy q (q0 α lam) with h | h | h
  · have := hM.1 ⟨hq.1, h.le⟩ ⟨hq00, le_rfl⟩ h
    simp only at this
    rw [hf0] at this
    exact ⟨⟨fun _ => h, fun _ => this⟩, ⟨fun h' => by linarith, fun h' => by linarith⟩⟩
  · rw [h, hf0]
    exact ⟨⟨fun h' => by linarith, fun h' => by linarith⟩,
      ⟨fun h' => by linarith, fun h' => by linarith⟩⟩
  · have h1 := (lemma_1 α lam q hα hlam ⟨hq.1, hq.2.le⟩).2 h.ne' hq.2.ne
    have h2 : zOf α lam q * q < 1 := by
      have := h1.mpr h
      rw [lt_div_iff₀ hz] at this
      linarith
    exact ⟨⟨fun h' => by linarith, fun h' => by linarith⟩, ⟨fun _ => h, fun _ => h2⟩⟩

theorem obp_proposition_3_part_3 (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (q1 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β) (hA2 : Assumption2 P q1)
    (pU pO : ℝ) (hU : IsEqPriceU P pU) (hO : IsEqPriceO P pO) :
    realizedProfitO P pO - realizedProfitU P pU =
        P.n / (4 * P.vbar * P.β) * (P.q * P.z - 1) *
          (P.vbar ^ 2 / P.z - P.c ^ 2 * P.β ^ 2 / P.q) ∧
      (realizedProfitU P pU < realizedProfitO P pO ↔ P.q < q0 P.α P.lam) := by
  have hS' := hS
  obtain ⟨hn, hv, hc, hβ, hβh, hq0, hqlt, hα0, hα1, hlam, hvp⟩ := hS'
  have hz1 := obp_z_ge_one P hS
  obtain ⟨r1, r2, _, _⟩ := obp_realized P hS hA1 q1 hq1 hA2 pU pO hU hO
  obtain ⟨v1, _, v3, _⟩ := obp_values P hS hA1
  have hid : realizedProfitO P pO - realizedProfitU P pU =
      P.n / (4 * P.vbar * P.β) * (P.q * P.z - 1) *
        (P.vbar ^ 2 / P.z - P.c ^ 2 * P.β ^ 2 / P.q) := by
    rw [r1, r2, v1, v3]
    unfold pStar pTilde
    have : P.z ≠ 0 := by linarith
    have : P.q ≠ 0 := hq0.ne'
    have : P.β ≠ 0 := hβ.ne'
    have : P.vbar ≠ 0 := hv.ne'
    field_simp
    ring
  refine ⟨hid, ?_⟩
  have hK := obp_K_pos P hS hA1
  rw [← sub_pos, hid, mul_comm (P.n / (4 * P.vbar * P.β)), mul_assoc, mul_pos_iff_of_pos_right hK,
    sub_pos, ← (obp_zq_sign P.α P.lam P.q ⟨hα0, hα1⟩ hlam ⟨hq0, hqlt⟩).1, mul_comm]
  rfl


end OutcomeRebate.Transfer

open OutcomeRebate.Transfer

theorem solution (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (q1 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β) (hA2 : Assumption2 P q1)
    (pU pO : ℝ) (hU : IsEqPriceU P pU) (hO : IsEqPriceO P pO) :
    realizedProfitO P pO - realizedProfitU P pU =
        P.n / (4 * P.vbar * P.β) * (P.q * P.z - 1) *
          (P.vbar ^ 2 / P.z - P.c ^ 2 * P.β ^ 2 / P.q) ∧
      (realizedProfitU P pU < realizedProfitO P pO ↔ P.q < q0 P.α P.lam) :=
  obp_proposition_3_part_3 P hS hA1 q1 hq1 hA2 pU pO hU hO
