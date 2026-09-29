-- Prove2me | solution 1 for WorkbookSource.plus_32274
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:23:30.167182+00:00
-- url     : https://prove2.me/submissions/5807052c-7de0-4acd-8a5d-1003319b8703

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution : ¬Nat.Prime (2^32 + 1)   := by
  norm_num
example : (¬Nat.Prime (2^32 + 1)) := @solution
#print axioms solution
