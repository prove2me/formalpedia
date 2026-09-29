-- Prove2me | solution 1 for WorkbookSource.base_32959
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:24:15.152298+00:00
-- url     : https://prove2.me/submissions/8785da3b-179e-4d13-bc48-2655b7f5b4cc

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution (x k : ℝ) : ‖3 * x ^ 2 + 4 - (3 * k ^ 2 + 4)‖ = 3 * ‖x - k‖ * ‖x + k‖  := by
  have h : 3*x^2+4-(3*k^2+4) = 3*(x-k)*(x+k) := by ring
  rw [h, norm_mul, norm_mul]
  norm_num
example : (∀ (x k : ℝ), ‖3 * x ^ 2 + 4 - (3 * k ^ 2 + 4)‖ = 3 * ‖x - k‖ * ‖x + k‖) := @solution
#print axioms solution
