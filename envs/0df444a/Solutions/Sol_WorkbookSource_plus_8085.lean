-- Prove2me | solution 1 for WorkbookSource.plus_8085
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:35.598596+00:00
-- url     : https://prove2.me/submissions/c5385e3c-bdb7-4d3f-8222-cff30cfe4c76

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y : ℝ) (h : x ^ 2 + 2 * x * y + 3 * y ^ 2 = 4) : x * y - 2 * x + 4 * y ≤ 20 / 3   := by
  have hw0 : 0 ≤ (x^2 + 2*x*y + 3*y^2 - 4) := by linarith only [h]
  have hw1 : 0 ≤ (-x^2 - 2*x*y - 3*y^2 + 4) := by linarith only [h]
  have hsum : 0 ≤ (14/3 : ℝ) * (1) * (3*x/14 - 3*y/7 + 1)^2 + (9/14 : ℝ) * (1) * (2*x/3 + y)^2 + (1/2 : ℝ) * ((-x^2 - 2*x*y - 3*y^2 + 4)) * (1)^2 := by positivity
  have hid : ( 20 / 3   ) - ( x * y - 2 * x + 4 * y ) = (14/3 : ℝ) * (1) * (3*x/14 - 3*y/7 + 1)^2 + (9/14 : ℝ) * (1) * (2*x/3 + y)^2 + (1/2 : ℝ) * ((-x^2 - 2*x*y - 3*y^2 + 4)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y : ℝ) (h : x ^ 2 + 2 * x * y + 3 * y ^ 2 = 4), x * y - 2 * x + 4 * y ≤ 20 / 3) := @solution
#print axioms solution
