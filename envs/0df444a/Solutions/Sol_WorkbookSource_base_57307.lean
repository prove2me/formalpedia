-- Prove2me | solution 1 for WorkbookSource.base_57307
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:23:27.159964+00:00
-- url     : https://prove2.me/submissions/da2b3308-c4c5-4b02-b036-98ae17511484

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution : (3 : ℝ) * (Real.sqrt 6 - Real.sqrt 2) > 3.1  := by
  have a := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have b := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have ha := Real.sqrt_nonneg (6:ℝ)
  have hb := Real.sqrt_nonneg (2:ℝ)
  have : (2449:ℝ)/1000 < √6 := by nlinarith
  have : √2 < (1415:ℝ)/1000 := by nlinarith
  linarith
example : ((3 : ℝ) * (Real.sqrt 6 - Real.sqrt 2) > 3.1) := @solution
#print axioms solution
