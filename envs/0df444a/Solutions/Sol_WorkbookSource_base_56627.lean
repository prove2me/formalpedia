-- Prove2me | solution 1 for WorkbookSource.base_56627
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:30:40.170023+00:00
-- url     : https://prove2.me/submissions/686ebbab-20eb-4386-ae14-bd327448b154

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096
theorem solution : (2:ℝ) ^ 2002 * 2002! < 2003 ^ 2002  := by
  norm_num [Nat.factorial]
example : ((2:ℝ) ^ 2002 * 2002! < 2003 ^ 2002) := @solution
#print axioms solution
