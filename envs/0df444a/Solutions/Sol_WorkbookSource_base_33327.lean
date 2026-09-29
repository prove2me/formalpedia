-- Prove2me | solution 1 for WorkbookSource.base_33327
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:36:12.635922+00:00
-- url     : https://prove2.me/submissions/65445a76-ba27-4581-8e57-99b407347ed5

import Mathlib
set_option autoImplicit false
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a ^ 12 + b ^ 12 + c ^ 12 + 8 * (a * b + b * c + c * a) ≥ 27  := by
  have power (x : ℝ) : 6 * x^2 - 5 ≤ x^12 := by
    have h := one_add_mul_sub_le_pow (a := x^2) (by nlinarith [sq_nonneg x]) 6
    norm_num only [Nat.cast_ofNat] at h
    rw [← pow_mul] at h
    norm_num at h
    nlinarith only [h]
  have hs : a*b + b*c + c*a ≤ 3 := by
    nlinarith [sq_nonneg (a-b), sq_nonneg (b-c), sq_nonneg (c-a), sq_nonneg (a+b+c-3)]
  nlinarith [power a, power b, power c]
#print axioms solution
