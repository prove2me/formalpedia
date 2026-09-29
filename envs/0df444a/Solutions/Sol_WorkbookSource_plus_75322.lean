-- Prove2me | solution 1 for WorkbookSource.plus_75322
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:31.011854+00:00
-- url     : https://prove2.me/submissions/fd8c5b85-28ee-4b16-8eb3-325d65c8b102

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a^2 + 2 * b^2 + 3 * c^2 = 36) : a * b + b * c + c * a + a + 20 * b + 51 * c ≤ 205   := by
  have hw0 : 0 ≤ (a^2 + 2*b^2 + 3*c^2 - 36) := by linarith only [h]
  have hw1 : 0 ≤ (-a^2 - 2*b^2 - 3*c^2 + 36) := by linarith only [h]
  have hsum : 0 ≤ (97 : ℝ) * (1) * (-a/194 - 10*b/97 - 51*c/194 + 1)^2 + (482/97 : ℝ) * (1) * (-107*a/964 + b - 607*c/964)^2 + (5661/1928 : ℝ) * (1) * (a - c/3)^2 + (3 : ℝ) * ((-a^2 - 2*b^2 - 3*c^2 + 36)) * (1)^2 := by positivity
  have hid : ( 205   ) - ( a * b + b * c + c * a + a + 20 * b + 51 * c ) = (97 : ℝ) * (1) * (-a/194 - 10*b/97 - 51*c/194 + 1)^2 + (482/97 : ℝ) * (1) * (-107*a/964 + b - 607*c/964)^2 + (5661/1928 : ℝ) * (1) * (a - c/3)^2 + (3 : ℝ) * ((-a^2 - 2*b^2 - 3*c^2 + 36)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a^2 + 2 * b^2 + 3 * c^2 = 36), a * b + b * c + c * a + a + 20 * b + 51 * c ≤ 205) := @solution
#print axioms solution
