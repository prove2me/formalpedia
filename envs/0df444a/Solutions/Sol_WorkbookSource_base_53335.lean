-- Prove2me | solution 1 for WorkbookSource.base_53335
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:23:25.791864+00:00
-- url     : https://prove2.me/submissions/19b8e232-9be9-4098-881d-a55730bca1b2

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution : ¬ (Real.sqrt 11 + Real.sqrt 13 = Real.sqrt 48)  := by
  have a := Real.sq_sqrt (show (0:ℝ) ≤ 11 by norm_num)
  have b := Real.sq_sqrt (show (0:ℝ) ≤ 13 by norm_num)
  have c := Real.sq_sqrt (show (0:ℝ) ≤ 48 by norm_num)
  have ha := Real.sqrt_nonneg (11:ℝ)
  have hb := Real.sqrt_nonneg (13:ℝ)
  have hc := Real.sqrt_nonneg (48:ℝ)
  have : √11 < (3317:ℝ)/1000 := by nlinarith
  have : √13 < (3606:ℝ)/1000 := by nlinarith
  have : (6928:ℝ)/1000 < √48 := by nlinarith
  intro h
  linarith
example : (¬ (Real.sqrt 11 + Real.sqrt 13 = Real.sqrt 48)) := @solution
#print axioms solution
