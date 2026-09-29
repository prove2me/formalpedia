-- Prove2me | solution 1 for WorkbookSource.plus_76773
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:24:13.633589+00:00
-- url     : https://prove2.me/submissions/e6c3f22c-c3cb-4024-8178-96d0098f6277

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution : ¬ (2^37 - 1).Prime   := by
  norm_num
example : (¬ (2^37 - 1).Prime) := @solution
#print axioms solution
