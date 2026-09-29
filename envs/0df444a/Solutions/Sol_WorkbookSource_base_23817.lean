-- Prove2me | solution 1 for WorkbookSource.base_23817
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:23:22.847329+00:00
-- url     : https://prove2.me/submissions/b3ab443f-4ec7-41d6-aec4-91df5a351a32

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution : ⌊√26 - √8⌋ = 2  := by
  apply Int.floor_eq_iff.mpr
  have a := Real.sq_sqrt (show (0:ℝ) ≤ 26 by norm_num)
  have b := Real.sq_sqrt (show (0:ℝ) ≤ 8 by norm_num)
  have ha := Real.sqrt_nonneg (26:ℝ)
  have hb := Real.sqrt_nonneg (8:ℝ)
  have : (5:ℝ) < √26 := by nlinarith
  have : √8 < (3:ℝ) := by nlinarith
  have : √26 < (55:ℝ)/10 := by nlinarith
  have : (25:ℝ)/10 < √8 := by nlinarith
  constructor <;> norm_num <;> linarith
example : (⌊√26 - √8⌋ = 2) := @solution
#print axioms solution
