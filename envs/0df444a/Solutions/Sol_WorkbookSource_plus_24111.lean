-- Prove2me | solution 1 for WorkbookSource.plus_24111
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:23:27.940684+00:00
-- url     : https://prove2.me/submissions/1bcdc7bd-8617-4ccf-9dd2-93eefa5ebff5

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution : ¬ Nat.Prime (2^10 + 5^12)   := by
  norm_num
example : (¬ Nat.Prime (2^10 + 5^12)) := @solution
#print axioms solution
