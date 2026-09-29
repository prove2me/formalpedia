-- Prove2me | solution 1 for WorkbookSource.base_26041
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:30:39.565266+00:00
-- url     : https://prove2.me/submissions/6547da9b-8735-4415-88bc-554e5fc0eed7

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096
theorem solution : 1004^2007 > 2007!  := by
  norm_num [Nat.factorial]
example : (1004^2007 > 2007!) := @solution
#print axioms solution
