-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P47.signed_bias_equal_weights
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T07:34:24.381312+00:00
-- url     : https://prove2.me/submissions/b78eb3a5-24c6-4f47-887c-f1d549710071

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

open scoped ComplexConjugate

open scoped BigOperators

open QAlgorithms.Papers.Independent.Intakethird100.P47 in
theorem solution (pA pB epsilon : ℝ)
    (hA : 0 < pA ∧ pA < 1) (hB : 0 < pB ∧ pB < 1)
    (he : 0 < epsilon)
    (heA : epsilon ≤ pA ∧ epsilon ≤ 1 - pA)
    (heB : epsilon ≤ pB ∧ epsilon ≤ 1 - pB)
    (t : (Bool × Bool) → ℝ) (ht : ∀ e, 0 ≤ t e) (hsum : ∑ e, t e = 1) :
    ((∀ A B, (∑ e, t e * biasedInput pA pB epsilon e A B) = binarySettingLaw pA pB A B) ↔
      ∀ e, t e = 1 / 4) := by
  have expand : ∀ A B, (∑ e, t e * biasedInput pA pB epsilon e A B) =
      t (true, true) * biasedInput pA pB epsilon (true, true) A B +
      t (true, false) * biasedInput pA pB epsilon (true, false) A B +
      t (false, true) * biasedInput pA pB epsilon (false, true) A B +
      t (false, false) * biasedInput pA pB epsilon (false, false) A B := by
    intro A B
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    ring
  have hsum' : t (true, true) + t (true, false) + t (false, true) + t (false, false) = 1 := by
    rw [Fintype.sum_prod_type] at hsum
    simp only [Fintype.sum_bool] at hsum
    linarith
  constructor
  · intro h
    have h_ff := h false false
    have h_tf := h true false
    have h_ft := h false true
    rw [expand] at h_ff h_tf h_ft
    simp only [biasedInput, binarySettingLaw, if_true, if_false, eq_self_iff_true,
      Bool.false_eq_true] at h_ff h_tf h_ft
    have hne : epsilon ≠ 0 := he.ne'
    have e2 : epsilon * (t (true, true) - t (true, false) + t (false, true) - t (false, false))
        = 0 := by
      linear_combination h_ff + h_tf - pB * hsum'
    have e1 : epsilon * (t (true, true) + t (true, false) - t (false, true) - t (false, false))
        = 0 := by
      linear_combination h_ff + h_ft - pA * hsum'
    have T2 := (mul_eq_zero.mp e2).resolve_left hne
    have T1 := (mul_eq_zero.mp e1).resolve_left hne
    have e12 : epsilon ^ 2 *
        (t (true, true) - t (true, false) - t (false, true) + t (false, false)) = 0 := by
      linear_combination h_ff - pA * pB * hsum' - pA * epsilon * T2 - pB * epsilon * T1
    have T12 := (mul_eq_zero.mp e12).resolve_left (pow_ne_zero 2 hne)
    rintro ⟨x, y⟩
    cases x <;> cases y <;> linarith
  · intro h A B
    rw [expand]
    simp only [h, biasedInput, binarySettingLaw, if_true, if_false, eq_self_iff_true,
      Bool.false_eq_true]
    cases A <;> cases B <;>
      simp only [if_true, if_false, eq_self_iff_true, Bool.false_eq_true] <;> ring
