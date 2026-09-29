-- Prove2me | solution 1 for WorkbookSource.base_908
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:36:23.421833+00:00
-- url     : https://prove2.me/submissions/2dcd2fb4-3827-45e4-a05e-d1196d3cbcca

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y : ℝ) (h : x^2 + y^2 + x * y + Real.sqrt 3 * (x + y) = 0) :
  x^2 + y^2 ≤ 3  := by
  have := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  nlinarith [sq_nonneg (x+y+√3)]
example : (∀ (x y : ℝ) (h : x^2 + y^2 + x * y + Real.sqrt 3 * (x + y) = 0), x^2 + y^2 ≤ 3) := @solution
#print axioms solution
