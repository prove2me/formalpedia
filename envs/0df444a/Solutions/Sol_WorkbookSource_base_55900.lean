-- Prove2me | solution 1 for WorkbookSource.base_55900
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:23:26.508138+00:00
-- url     : https://prove2.me/submissions/a0446dea-fab3-476c-9197-e1bb6d9b4155

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution : (72 * Real.sqrt 5 : ℝ) < 161  := by
  have := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have := Real.sqrt_nonneg (5:ℝ)
  nlinarith
example : ((72 * Real.sqrt 5 : ℝ) < 161) := @solution
#print axioms solution
