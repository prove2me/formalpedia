-- Prove2me | solution 1 for WorkbookSource.plus_44251
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:41.01624+00:00
-- url     : https://prove2.me/submissions/2845a5fa-1229-4e5a-aae2-fbf458ab20f9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) : x + 6 * y + 10 * x * y ≤ 51 / 5   := by
  have hw0 : 0 ≤ (x^2 + y^2 - 1) := by linarith only [h]
  have hw1 : 0 ≤ (-x^2 - y^2 + 1) := by linarith only [h]
  have hsum : 0 ≤ (15/2 : ℝ) * (1) * (-2*x/3 + y - 2/5)^2 + (25/6 : ℝ) * (1) * (x - 3/5)^2 + (15/2 : ℝ) * ((-x^2 - y^2 + 1)) * (1)^2 := by positivity
  have hid : ( 51 / 5   ) - ( x + 6 * y + 10 * x * y ) = (15/2 : ℝ) * (1) * (-2*x/3 + y - 2/5)^2 + (25/6 : ℝ) * (1) * (x - 3/5)^2 + (15/2 : ℝ) * ((-x^2 - y^2 + 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1), x + 6 * y + 10 * x * y ≤ 51 / 5) := @solution
#print axioms solution
