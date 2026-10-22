-- Prove2me | solution 1 for OutcomeRebate.Transfer.joint_surplus_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:41:08.594137+00:00
-- url     : https://prove2.me/submissions/22a7e602-ba8d-44a8-a01a-7fb981a71c4c

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Theorems.Thm_OutcomeRebate_Transfer_closed_forms_uniform
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

theorem obp_joint_surplus_identity (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) :
    firmProfitO P P.β (pTilde P) + payerObjO P P.β (pTilde P) -
        (firmProfitU P P.β (pStar P) + payerObjU P P.β (pStar P)) =
      P.n * P.β * P.c / (4 * P.vbar) * (P.q * P.z - 1) *
        (2 * P.vp + P.vbar - 2 * P.c / P.q + P.β * P.c / (2 * P.q) + P.β * P.c * P.z / 2) := by
  have hS' := hS
  obtain ⟨hn, hv, hc, hβ, hβh, hq0, hqlt, hα0, hα1, hlam, hvp⟩ := hS'
  have hz1 := obp_z_ge_one P hS
  obtain ⟨v1, v2, v3, v4⟩ := obp_values P hS hA1
  rw [v1, v2, v3, v4]
  unfold pStar pTilde
  have : P.z ≠ 0 := by linarith
  have : P.q ≠ 0 := hq0.ne'
  have : P.β ≠ 0 := hβ.ne'
  have : P.vbar ≠ 0 := hv.ne'
  field_simp
  ring


end OutcomeRebate.Transfer

open OutcomeRebate.Transfer

theorem solution (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) :
    firmProfitO P P.β (pTilde P) + payerObjO P P.β (pTilde P) -
        (firmProfitU P P.β (pStar P) + payerObjU P P.β (pStar P)) =
      P.n * P.β * P.c / (4 * P.vbar) * (P.q * P.z - 1) *
        (2 * P.vp + P.vbar - 2 * P.c / P.q + P.β * P.c / (2 * P.q) + P.β * P.c * P.z / 2) :=
  obp_joint_surplus_identity P hS hA1
