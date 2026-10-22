-- Prove2me | solution 1 for OutcomeRebate.Transfer.purchase_rule_uniform
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:41:20.600891+00:00
-- url     : https://prove2.me/submissions/c8bf5863-1951-4c6e-809f-2f6c6266a312

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

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

lemma obp_u_nonneg (α lam x : ℝ) (hx : 0 ≤ x) : u α lam x = x ^ α := by
  simp [u, hx]

lemma obp_u_neg (α lam x : ℝ) (hx : x < 0) : u α lam x = -(lam * (-x) ^ α) := by
  simp [u, not_le.mpr hx]

theorem obp_purchase_rule_uniform (P : Params) (hS : P.Standing) (bb p v : ℝ)
    (hbb : bb = P.β ∨ bb = 1) (hp : 0 ≤ p) (hv : 0 ≤ v) :
    0 ≤ welfareU P bb p v ↔ bb * p * P.z ≤ v := by
  have hS' := hS
  obtain ⟨_, _, _, hβ, hβh, hq0, hq1, hα0, hα1, hlam, _⟩ := hS'
  have hbbpos : 0 < bb := by rcases hbb with h | h <;> rw [h] <;> linarith
  have hz1 := obp_z_ge_one P hS
  unfold welfareU
  set x := bb * p with hxdef
  have hx0 : 0 ≤ x := mul_nonneg hbbpos.le hp
  rcases eq_or_lt_of_le hx0 with hx | hx
  · rw [← hx]
    simp only [sub_zero, neg_zero, zero_mul]
    rw [obp_u_nonneg _ _ _ hv, obp_u_nonneg _ _ _ le_rfl, Real.zero_rpow hα0.ne']
    simp only [mul_zero, add_zero, hv, iff_true]
    exact mul_nonneg hq0.le (Real.rpow_nonneg hv _)
  · rw [obp_u_neg _ _ _ (by linarith : -x < 0), neg_neg]
    have hxa : 0 < x ^ P.α := Real.rpow_pos_of_pos hx _
    by_cases hvx : x ≤ v
    · rw [obp_u_nonneg _ _ _ (by linarith : 0 ≤ v - x)]
      set k := P.lam * (1 - P.q) / P.q with hk
      have hkpos : 0 < k := obp_k_pos P hS
      have hkq : k * P.q = P.lam * (1 - P.q) := by
        rw [hk]; field_simp
      have hkx : (k ^ (1 / P.α) * x) ^ P.α = k * x ^ P.α := by
        rw [Real.mul_rpow (Real.rpow_nonneg hkpos.le _) hx0, one_div,
          Real.rpow_inv_rpow hkpos.le hα0.ne']
      have hz : P.z = 1 + k ^ (1 / P.α) := rfl
      have key : 0 ≤ P.q * (v - x) ^ P.α + (1 - P.q) * -(P.lam * x ^ P.α) ↔
          (k ^ (1 / P.α) * x) ^ P.α ≤ (v - x) ^ P.α := by
        rw [hkx]
        constructor
        · intro h
          have : P.q * (k * x ^ P.α) ≤ P.q * (v - x) ^ P.α := by nlinarith
          exact le_of_mul_le_mul_left this hq0
        · intro h
          nlinarith
      rw [key, Real.rpow_le_rpow_iff (mul_nonneg (Real.rpow_nonneg hkpos.le _) hx0)
        (by linarith) hα0, hz]
      constructor <;> intro h <;> nlinarith
    · push_neg at hvx
      rw [obp_u_neg _ _ _ (by linarith : v - x < 0)]
      have h1 : 0 ≤ (-(v - x)) ^ P.α := Real.rpow_nonneg (by linarith) _
      constructor
      · intro h
        exfalso
        have : 0 < (1 - P.q) * (P.lam * x ^ P.α) :=
          mul_pos (by linarith) (mul_pos (by linarith) hxa)
        nlinarith [mul_nonneg hq0.le (mul_nonneg (by linarith : (0:ℝ) ≤ P.lam) h1)]
      · intro h
        exfalso
        nlinarith


end OutcomeRebate.Transfer

open OutcomeRebate.Transfer

theorem solution (P : Params) (hS : P.Standing) (bb p v : ℝ)
    (hbb : bb = P.β ∨ bb = 1) (hp : 0 ≤ p) (hv : 0 ≤ v) :
    0 ≤ welfareU P bb p v ↔ bb * p * P.z ≤ v :=
  obp_purchase_rule_uniform P hS bb p v hbb hp hv
