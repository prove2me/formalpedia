-- Prove2me | solution 1 for WorkbookSource.base_46845
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:23:24.196666+00:00
-- url     : https://prove2.me/submissions/2ea5686d-da5d-497f-82d4-2db1a4e749a8

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution : 0 < √6 - √2 - √3 + 1  := by
  have a := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have b := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have c := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have ha := Real.sqrt_nonneg (6:ℝ)
  have hb := Real.sqrt_nonneg (2:ℝ)
  have hc := Real.sqrt_nonneg (3:ℝ)
  have : (244:ℝ)/100 < √6 := by nlinarith
  have : √2 < (142:ℝ)/100 := by nlinarith
  have : √3 < (174:ℝ)/100 := by nlinarith
  linarith
example : (0 < √6 - √2 - √3 + 1) := @solution
#print axioms solution
