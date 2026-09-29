-- Prove2me | solution 1 for WorkbookSource.plus_18240
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:30:40.918618+00:00
-- url     : https://prove2.me/submissions/cb00d573-f0b8-4836-bf42-a07fc3f161f4

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096
theorem solution : (6!)^5! ∣ (6!)!   := by
  norm_num [Nat.factorial]
example : ((6!)^5! ∣ (6!)!) := @solution
#print axioms solution
