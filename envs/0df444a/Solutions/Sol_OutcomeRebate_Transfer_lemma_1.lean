-- Prove2me | solution 1 for OutcomeRebate.Transfer.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:41:19.80119+00:00
-- url     : https://prove2.me/submissions/6da10361-bdb8-475d-8280-f3eaaccaa7c5

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer
open MeasureTheory

/-- Key identity: `(λ r)^{1/α} = r (r/L)^{(1-α)/α}` with `L = λ^{-1/(1-α)}`. -/
lemma obp_key_identity (α lam r : ℝ) (hα : 0 < α ∧ α < 1) (hlam : 1 ≤ lam) (hr : 0 < r) :
    (lam * r) ^ (1 / α) = r * (r / lam ^ (-(1 / (1 - α)))) ^ ((1 - α) / α) := by
  have hl : 0 < lam := by linarith
  have h1a : (1 - α) ≠ 0 := by linarith
  have hα0 : α ≠ 0 := hα.1.ne'
  rw [Real.rpow_neg hl.le, div_inv_eq_mul, Real.mul_rpow hr.le (Real.rpow_nonneg hl.le _),
    ← Real.rpow_mul hl.le, ← mul_assoc]
  conv_lhs => rw [Real.mul_rpow hl.le hr.le]
  have e1 : 1 / (1 - α) * ((1 - α) / α) = 1 / α := by field_simp
  have e2 : r * r ^ ((1 - α) / α) = r ^ (1 / α) := by
    conv_lhs => arg 1; rw [← Real.rpow_one r]
    rw [← Real.rpow_add hr]
    congr 1
    field_simp
    ring
  rw [e1, e2, mul_comm]

lemma obp_zq_formula (α lam q : ℝ) (hα : 0 < α ∧ α < 1) (hlam : 1 ≤ lam) (hq : 0 < q ∧ q < 1) :
    zOf α lam q * q = q + (1 - q) *
      (((1 - q) / q) / lam ^ (-(1 / (1 - α)))) ^ ((1 - α) / α) := by
  have hr : 0 < (1 - q) / q := div_pos (by linarith) hq.1
  unfold zOf
  rw [mul_div_assoc, obp_key_identity α lam _ hα hlam hr]
  have hqne : q ≠ 0 := hq.1.ne'
  field_simp

lemma obp_q0_iff (α lam q : ℝ) (hα : 0 < α ∧ α < 1) (hlam : 1 ≤ lam) (hq : 0 < q ∧ q < 1) :
    (q < q0 α lam ↔ lam ^ (-(1 / (1 - α))) < (1 - q) / q) ∧
      (q0 α lam < q ↔ (1 - q) / q < lam ^ (-(1 / (1 - α)))) := by
  have hL : 0 < lam ^ (-(1 / (1 - α))) := Real.rpow_pos_of_pos (by linarith) _
  set L := lam ^ (-(1 / (1 - α)))
  unfold q0
  have hq0 := hq.1
  constructor
  · rw [lt_div_iff₀ (by linarith), lt_div_iff₀ hq0]
    constructor <;> intro h <;> nlinarith
  · rw [div_lt_iff₀ (by linarith), div_lt_iff₀ hq0]
    constructor <;> intro h <;> nlinarith

/-- Sign of `zq - 1` versus the threshold `q₀`. -/
theorem obp_zq_sign (α lam q : ℝ) (hα : 0 < α ∧ α < 1) (hlam : 1 ≤ lam) (hq : 0 < q ∧ q < 1) :
    (1 < zOf α lam q * q ↔ q < q0 α lam) ∧ (zOf α lam q * q < 1 ↔ q0 α lam < q) := by
  have hr : 0 < (1 - q) / q := div_pos (by linarith) hq.1
  have hL : 0 < lam ^ (-(1 / (1 - α))) := Real.rpow_pos_of_pos (by linarith) _
  have he : 0 < (1 - α) / α := div_pos (by linarith) hα.1
  have hs : 0 < ((1 - q) / q) / lam ^ (-(1 / (1 - α))) := div_pos hr hL
  rw [obp_zq_formula α lam q hα hlam hq, (obp_q0_iff α lam q hα hlam hq).1,
    (obp_q0_iff α lam q hα hlam hq).2]
  have h1q : 0 < 1 - q := by linarith
  constructor
  · rw [← one_lt_div hL]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      have := Real.rpow_le_one hs.le hc he.le
      nlinarith
    · intro h
      have := Real.one_lt_rpow h he
      nlinarith
  · rw [← div_lt_one hL]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      have := Real.one_le_rpow hc he.le
      nlinarith
    · intro h
      have := Real.rpow_lt_one hs.le h he
      nlinarith

/-- Monotonicity of `zq` below a point where `zq ≥ 1`. -/
theorem obp_zq_anti (α lam q q' : ℝ) (hα : 0 < α ∧ α < 1) (hlam : 1 ≤ lam)
    (hq' : 0 < q') (hqq : q' ≤ q) (hq : q < 1) (h1 : 1 ≤ zOf α lam q * q) :
    zOf α lam q * q ≤ zOf α lam q' * q' := by
  have hq0 : 0 < q := lt_of_lt_of_le hq' hqq
  have hl : 0 < lam := by linarith
  set r := (1 - q) / q with hr
  set r' := (1 - q') / q' with hr'
  have hrpos : 0 < r := div_pos (by linarith) hq0
  have hqr : q * (1 + r) = 1 := by rw [hr]; field_simp; ring
  have hqr' : q' * (1 + r') = 1 := by rw [hr']; field_simp; ring
  have hrr : r ≤ r' := by
    rw [hr, hr', div_le_div_iff₀ hq0 hq']; nlinarith
  set t := r' / r with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hrpos]; linarith
  have hrt : r' = t * r := by rw [ht]; field_simp
  set A := (lam * r) ^ (1 / α) with hA
  have hApos : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  have hz : zOf α lam q = 1 + A := by unfold zOf; rw [mul_div_assoc]
  have hz' : zOf α lam q' = 1 + (lam * r') ^ (1 / α) := by unfold zOf; rw [mul_div_assoc]
  have hA' : t * A ≤ (lam * r') ^ (1 / α) := by
    rw [hrt, show lam * (t * r) = t * (lam * r) by ring,
      Real.mul_rpow (by linarith) (by positivity)]
    apply mul_le_mul_of_nonneg_right _ hApos
    conv_lhs => rw [← Real.rpow_one t]
    apply Real.rpow_le_rpow_of_exponent_le ht1
    rw [le_div_iff₀ hα.1]; linarith
  rw [hz] at h1 ⊢
  rw [hz']
  have hAr : r ≤ A := by nlinarith
  have step : q * (1 + A) ≤ q' * (1 + t * A) := by
    have e : q' * (1 + t * A) - q * (1 + A) = q * q' * ((t - 1) * (A - r)) := by
      have e1 : q' * (1 + t * A) = q' * (1 + t * A) * (q * (1 + r)) := by rw [hqr]; ring
      have e2 : q * (1 + A) = q * (1 + A) * (q' * (1 + t * r)) := by
        rw [← hrt, hqr']; ring
      rw [e1, e2]; ring
    have : 0 ≤ q * q' * ((t - 1) * (A - r)) :=
      mul_nonneg (mul_nonneg hq0.le hq'.le) (mul_nonneg (by linarith) (by linarith))
    linarith
  calc (1 + A) * q = q * (1 + A) := by ring
    _ ≤ q' * (1 + t * A) := step
    _ ≤ q' * (1 + (lam * r') ^ (1 / α)) := by nlinarith
    _ = (1 + (lam * r') ^ (1 / α)) * q' := by ring

lemma obp_q0_bounds (α lam : ℝ) (hα : 0 < α ∧ α < 1) (hlam : 1 ≤ lam) :
    0 < q0 α lam ∧ q0 α lam < 1 := by
  have hL : 0 < lam ^ (-(1 / (1 - α))) := Real.rpow_pos_of_pos (by linarith) _
  unfold q0
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]; linarith

lemma obp_zq_at_one (α lam : ℝ) (hα : 0 < α ∧ α < 1) : zOf α lam 1 * 1 = 1 := by
  unfold zOf
  have h : (1 / α) ≠ 0 := by have := hα.1; positivity
  simp only [sub_self, mul_zero, zero_div, mul_one]
  rw [Real.zero_rpow h]; ring

lemma obp_zq_at_q0 (α lam : ℝ) (hα : 0 < α ∧ α < 1) (hlam : 1 ≤ lam) :
    zOf α lam (q0 α lam) * q0 α lam = 1 := by
  obtain ⟨h0, h1⟩ := obp_q0_bounds α lam hα hlam
  have hL : 0 < lam ^ (-(1 / (1 - α))) := Real.rpow_pos_of_pos (by linarith) _
  rw [obp_zq_formula α lam _ hα hlam ⟨h0, h1⟩]
  have hr : (1 - q0 α lam) / q0 α lam = lam ^ (-(1 / (1 - α))) := by
    unfold q0; field_simp; ring
  rw [hr, div_self hL.ne', Real.one_rpow]; ring

lemma obp_z_pos' (α lam q : ℝ) (hlam : 1 ≤ lam) (hq : 0 < q ∧ q ≤ 1) : 0 < zOf α lam q := by
  unfold zOf
  have : 0 ≤ lam * (1 - q) / q := div_nonneg (mul_nonneg (by linarith) (by linarith)) hq.1.le
  have := Real.rpow_nonneg this (1 / α)
  linarith

theorem obp_lemma_1 (α lam q : ℝ) (hα : 0 < α ∧ α < 1) (hlam : 1 ≤ lam) (hq : 0 < q ∧ q ≤ 1) :
    ((q = q0 α lam ∨ q = 1) → 1 / zOf α lam q = q) ∧
      (q ≠ q0 α lam → q ≠ 1 → (q < 1 / zOf α lam q ↔ q0 α lam < q)) := by
  have hz := obp_z_pos' α lam q hlam hq
  constructor
  · intro h
    have h1 : zOf α lam q * q = 1 := by
      rcases h with h | h <;> rw [h]
      · exact obp_zq_at_q0 α lam hα hlam
      · exact obp_zq_at_one α lam hα
    field_simp
    linarith
  · intro _ h1
    have hq1 : q < 1 := lt_of_le_of_ne hq.2 h1
    rw [← (obp_zq_sign α lam q hα hlam ⟨hq.1, hq1⟩).2, lt_div_iff₀ hz, mul_comm]


end OutcomeRebate.Transfer

open OutcomeRebate.Transfer

theorem solution (α lam q : ℝ) (hα : 0 < α ∧ α < 1) (hlam : 1 ≤ lam) (hq : 0 < q ∧ q ≤ 1) :
    ((q = q0 α lam ∨ q = 1) → 1 / zOf α lam q = q) ∧
      (q ≠ q0 α lam → q ≠ 1 → (q < 1 / zOf α lam q ↔ q0 α lam < q)) :=
  obp_lemma_1 α lam q hα hlam hq
