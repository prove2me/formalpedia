-- Prove2me | solution 1 for WorkbookSource.base_44709
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:23:23.583006+00:00
-- url     : https://prove2.me/submissions/e45ec0a3-024f-404a-8899-c77be33d621b

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution : Real.sqrt 17 + Real.sqrt 10 > Real.sqrt 53  := by
  have a := Real.sq_sqrt (show (0:ℝ) ≤ 17 by norm_num)
  have b := Real.sq_sqrt (show (0:ℝ) ≤ 10 by norm_num)
  have c := Real.sq_sqrt (show (0:ℝ) ≤ 53 by norm_num)
  have ha := Real.sqrt_nonneg (17:ℝ)
  have hb := Real.sqrt_nonneg (10:ℝ)
  have hc := Real.sqrt_nonneg (53:ℝ)
  have : (4123:ℝ)/1000 < √17 := by nlinarith
  have : (3162:ℝ)/1000 < √10 := by nlinarith
  have : √53 < (7281:ℝ)/1000 := by nlinarith
  linarith
example : (Real.sqrt 17 + Real.sqrt 10 > Real.sqrt 53) := @solution
#print axioms solution
