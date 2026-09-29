-- Prove2me | solution 1 for WorkbookSource.plus_44551
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:23:30.898452+00:00
-- url     : https://prove2.me/submissions/882e53ba-b417-4b34-b844-f7080147aaa2

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution : ¬ Nat.Prime (2^65 + 1)   := by
  norm_num
example : (¬ Nat.Prime (2^65 + 1)) := @solution
#print axioms solution
