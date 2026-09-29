-- Prove2me | solution 1 for WorkbookSource.base_1949
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:30:38.717583+00:00
-- url     : https://prove2.me/submissions/3e6e38fc-4bc6-4e77-ac85-97884eb489cc

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096
theorem solution : ¬(1000! ≡ -2 [ZMOD 2003])  := by
  norm_num [Int.ModEq, Nat.factorial]
example : (¬(1000! ≡ -2 [ZMOD 2003])) := @solution
#print axioms solution
