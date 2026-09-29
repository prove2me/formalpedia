-- Prove2me | solution 1 for WorkbookSource.base_878
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:36:22.470261+00:00
-- url     : https://prove2.me/submissions/b0871a37-9906-4292-8b1a-3c85148f0a26

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (h : a * b + a * c + a * d + b * c + b * d + c * d = -1) : |a| + |b| + |c| + |d| ≥ 2  := by
  have h1 : -(a*b) ≤ |a| * |b| := by rw [← abs_mul]; exact neg_le_abs _
  have h2 : -(a*c) ≤ |a| * |c| := by rw [← abs_mul]; exact neg_le_abs _
  have h3 : -(a*d) ≤ |a| * |d| := by rw [← abs_mul]; exact neg_le_abs _
  have h4 : -(b*c) ≤ |b| * |c| := by rw [← abs_mul]; exact neg_le_abs _
  have h5 : -(b*d) ≤ |b| * |d| := by rw [← abs_mul]; exact neg_le_abs _
  have h6 : -(c*d) ≤ |c| * |d| := by rw [← abs_mul]; exact neg_le_abs _
  have hp : 0 ≤ |a|+|b|+|c|+|d| := by positivity
  nlinarith [sq_nonneg (a+b+c+d),sq_abs a,sq_abs b,sq_abs c,sq_abs d]
example : (∀ (a b c d : ℝ) (h : a * b + a * c + a * d + b * c + b * d + c * d = -1), |a| + |b| + |c| + |d| ≥ 2) := @solution
#print axioms solution
