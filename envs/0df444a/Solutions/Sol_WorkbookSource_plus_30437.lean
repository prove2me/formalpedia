-- Prove2me | solution 1 for WorkbookSource.plus_30437
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:23:29.45323+00:00
-- url     : https://prove2.me/submissions/20b5fb96-da0a-489e-831d-07e6e1c6080d

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution : 5 * Real.sqrt 2 - Real.sqrt 11 < 5 * Real.sqrt 3 - 3   := by
  have a := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have b := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have c := Real.sq_sqrt (show (0:ℝ) ≤ 11 by norm_num)
  have ha := Real.sqrt_nonneg (2:ℝ)
  have hb := Real.sqrt_nonneg (3:ℝ)
  have hc := Real.sqrt_nonneg (11:ℝ)
  have : √2 < (15:ℝ)/10 := by nlinarith
  have : (17:ℝ)/10 < √3 := by nlinarith
  have : (33:ℝ)/10 < √11 := by nlinarith
  linarith
example : (5 * Real.sqrt 2 - Real.sqrt 11 < 5 * Real.sqrt 3 - 3) := @solution
#print axioms solution
