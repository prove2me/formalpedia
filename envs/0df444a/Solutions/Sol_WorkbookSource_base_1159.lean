-- Prove2me | solution 1 for WorkbookSource.base_1159
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:39:06.216239+00:00
-- url     : https://prove2.me/submissions/fdc5bb9c-3c4f-492a-8af7-ea4e5ca30412

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x : ℝ) (hx: x > 0) : (4:ℝ)^(x + 1) > 3^(Real.sqrt (x^2 + 1))  := by
  have ht := Real.sq_sqrt (show (0:ℝ) ≤ x^2+1 by positivity)
  have hp := Real.sqrt_nonneg (x^2+1)
  have hs : Real.sqrt (x^2+1) < x+1 := by nlinarith
  exact lt_trans (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<3) hs) (Real.rpow_lt_rpow (by norm_num) (by norm_num) (by linarith))
example : (∀ (x : ℝ) (hx: x > 0), (4:ℝ)^(x + 1) > 3^(Real.sqrt (x^2 + 1))) := @solution
#print axioms solution
