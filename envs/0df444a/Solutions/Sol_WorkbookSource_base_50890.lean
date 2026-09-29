-- Prove2me | solution 1 for WorkbookSource.base_50890
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:23:25.010171+00:00
-- url     : https://prove2.me/submissions/97a5789e-667e-4614-a5a1-960c95680f8e

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution : 2 ^ (2 ^ 151) > 3 ^ (2 ^ 150)  := by
  have h : (2:ℕ)^151 = 2 * 2^150 := by rw [pow_succ]; ring
  rw [h, pow_mul]
  exact pow_lt_pow_left₀ (by norm_num : (3:ℕ) < 2^2) (by norm_num) (by positivity)
example : (2 ^ (2 ^ 151) > 3 ^ (2 ^ 150)) := @solution
#print axioms solution
