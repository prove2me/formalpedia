-- Prove2me | solution 1 for WorkbookSource.base_9065
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:23:22.155958+00:00
-- url     : https://prove2.me/submissions/8acacbc7-2310-41f9-a5a0-1b79e2b375e8

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution : 2^(3^100) > 2^(2^151)  := by
  exact pow_lt_pow_right₀ (by norm_num) (by norm_num)
example : (2^(3^100) > 2^(2^151)) := @solution
#print axioms solution
