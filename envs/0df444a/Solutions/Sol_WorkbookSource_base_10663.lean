-- Prove2me | solution 1 for WorkbookSource.base_10663
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:38:06.68077+00:00
-- url     : https://prove2.me/submissions/07355aa0-0d9a-455b-aa19-9bf89dd4811a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y : ℝ) (h : x + y ≥ 0) :
  x ^ 5 + y ^ 5 - x ^ 4 * y - x * y ^ 4 + x ^ 2 + 4 * x + 7 ≥ 3  := by
  have hw0 : 0 ≤ (x + y) := by linarith only [h]
  have hsum : 0 ≤ (4 : ℝ) * (1) * (x/2 + 1)^2 + (2 : ℝ) * ((x + y)) * (-x^2/2 + x*y - y^2/2)^2 + (1/2 : ℝ) * ((x + y)) * (-x^2 + y^2)^2 := by positivity
  have hid : (
  x ^ 5 + y ^ 5 - x ^ 4 * y - x * y ^ 4 + x ^ 2 + 4 * x + 7 ) - ( 3  ) = (4 : ℝ) * (1) * (x/2 + 1)^2 + (2 : ℝ) * ((x + y)) * (-x^2/2 + x*y - y^2/2)^2 + (1/2 : ℝ) * ((x + y)) * (-x^2 + y^2)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y : ℝ) (h : x + y ≥ 0), x ^ 5 + y ^ 5 - x ^ 4 * y - x * y ^ 4 + x ^ 2 + 4 * x + 7 ≥ 3) := @solution
#print axioms solution
