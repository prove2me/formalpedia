-- Prove2me | solution 1 for OutcomeRebate.Transfer.joint_surplus_bracket_pos
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:41:10.057139+00:00
-- url     : https://prove2.me/submissions/5853c9a0-2086-463b-9953-17da1724cd69

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
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

lemma obp_pStar_w (P : Params) (hS : P.Standing) :
    pStar P = P.c / 2 + P.vbar / (P.β * P.z) / 2 ∧
      P.vbar = P.β * P.z * (P.vbar / (P.β * P.z)) := by
  have hz1 := obp_z_ge_one P hS
  obtain ⟨_, hv, hc, hβ, _, _, _, _, _, _, _⟩ := hS
  have : P.β * P.z ≠ 0 := by positivity
  constructor
  · unfold pStar; field_simp
  · field_simp

theorem obp_joint_surplus_bracket_pos (P : Params) (hS : P.Standing) (hA1 : Assumption1 P)
    (q1 : ℝ) (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β)
    (hA2 : Assumption2 P q1) :
    0 < 2 * P.vp + P.vbar - 2 * P.c / P.q + P.β * P.c / (2 * P.q) + P.β * P.c * P.z / 2 := by
  have hS' := hS
  obtain ⟨hn, hv, hc, hβ, hβh, hq0, hqlt, hα0, hα1, hlam, hvp⟩ := hS'
  have hz1 := obp_z_ge_one P hS
  obtain ⟨hA, hA'⟩ := obp_A1 P hS hA1
  set Q := 1 / P.q with hQ
  have hQq : Q * P.q = 1 := by rw [hQ]; field_simp
  have hcQ : 2 * P.c / P.q = 2 * (P.c * Q) := by rw [hQ]; ring
  have hcQ2 : P.β * P.c / (2 * P.q) = P.β * P.c * Q / 2 := by rw [hQ]; field_simp
  rw [hcQ, hcQ2]
  rcases le_or_gt 1 (P.z * P.q) with hzq | hzq
  · -- high-risk (or boundary) case: use the first half of Assumption 2
    have h := hA2.1
    set B := 1 / P.β with hB
    have hBβ : B * P.β = 1 := by rw [hB]; field_simp
    have hB2 : 2 ≤ B := by rw [hB, le_div_iff₀ hβ]; linarith
    have hpt : pTilde P = P.c * Q / 2 + P.vbar * B / 2 := by
      unfold pTilde; rw [hQ, hB]; field_simp
    rw [hpt] at h
    -- c z ≥ c Q
    have hcz : P.c * Q ≤ P.c * P.z := by
      have : Q ≤ P.z := by
        have := mul_le_mul_of_nonneg_left hzq (by positivity : (0:ℝ) ≤ Q)
        nlinarith
      exact mul_le_mul_of_nonneg_left this hc.le
    -- v̄ > β c Q
    have hvb : P.β * (P.c * Q) < P.vbar := by
      have := mul_lt_mul_of_pos_right hA (by positivity : (0:ℝ) < Q)
      nlinarith
    have hprod : 0 < (P.vbar - P.β * (P.c * Q)) * (B - 1 / 2) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  · -- low-risk case: the second half of Assumption 2 must be the price condition
    have h : pStar P * (1 / P.q - P.z * P.β / 2) - P.vbar / 2 ≤ P.vp := by
      rcases hA2.2 with h | h
      · exfalso
        have hk : (1:ℝ) < 2 / P.β := by rw [lt_div_iff₀ hβ]; linarith
        have := ((zq_monotone P.α P.lam ⟨hα0, hα1⟩ hlam).2.2.2 (2 / P.β) q1 hk hq1.1 hq1.2.1
          hq1.2.2 P.q hq0 hqlt).mpr h
        have : (1:ℝ) < P.z * P.q := lt_of_lt_of_le hk this
        linarith
      · exact h
    obtain ⟨hpsw, hw⟩ := obp_pStar_w P hS
    set w := P.vbar / (P.β * P.z)
    rw [hpsw, ← hQ] at h
    have hzQ : P.z < Q := by
      have := mul_lt_mul_of_pos_right hzq (by positivity : (0:ℝ) < Q)
      nlinarith
    have hwc : P.c < w := by rw [hw] at hA'; nlinarith [mul_pos hβ (by linarith : (0:ℝ) < P.z)]
    have hpos : 0 < Q - P.z * P.β / 2 := by nlinarith
    have hprod : 0 < (w - P.c) * (Q - P.z * P.β / 2) := mul_pos (by linarith) hpos
    have e : P.vbar = w * P.z * P.β := by rw [hw]; ring
    rw [e] at h ⊢
    nlinarith [mul_pos (mul_pos hβ hc) (sub_pos.mpr hzQ)]


end OutcomeRebate.Transfer

open OutcomeRebate.Transfer

theorem solution (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (q1 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β) (hA2 : Assumption2 P q1) :
    0 < 2 * P.vp + P.vbar - 2 * P.c / P.q + P.β * P.c / (2 * P.q) + P.β * P.c * P.z / 2 :=
  obp_joint_surplus_bracket_pos P hS hA1 q1 hq1 hA2
