-- Prove2me | solution 1 for WorkbookSource.plus_24738
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:23:28.696437+00:00
-- url     : https://prove2.me/submissions/2c0d4dba-e5b9-44d2-97b4-3d50b62c753f

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution : √2 + √3 < 1 + √5   := by
  have a := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have b := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have c := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have ha := Real.sqrt_nonneg (2:ℝ)
  have hb := Real.sqrt_nonneg (3:ℝ)
  have hc := Real.sqrt_nonneg (5:ℝ)
  have : √2 < (1415:ℝ)/1000 := by nlinarith
  have : √3 < (1733:ℝ)/1000 := by nlinarith
  have : (2235:ℝ)/1000 < √5 := by nlinarith
  linarith
example : (√2 + √3 < 1 + √5) := @solution
#print axioms solution
