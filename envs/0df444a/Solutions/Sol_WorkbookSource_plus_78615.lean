-- Prove2me | solution 1 for WorkbookSource.plus_78615
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:24:14.377654+00:00
-- url     : https://prove2.me/submissions/bd800442-33bc-42fe-be35-49ae15506a08

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution : ¬ Nat.Prime (2^29 - 1)   := by
  norm_num
example : (¬ Nat.Prime (2^29 - 1)) := @solution
#print axioms solution
