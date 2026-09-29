-- Prove2me | solution 1 for WorkbookSource.base_16267
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:28.434449+00:00
-- url     : https://prove2.me/submissions/18aecd8c-2f63-4c6d-a61a-0537c38ac69e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y : ℝ) (h : 5 * x ^ 2 + 4 * x * y + 11 * y ^ 2 = 3) :
  x * y - 2 * x + 5 * y ≤ 13 / 4  := by
  have hw0 : 0 ≤ (5*x^2 + 4*x*y + 11*y^2 - 3) := by linarith only [h]
  have hw1 : 0 ≤ (-5*x^2 - 4*x*y - 11*y^2 + 3) := by linarith only [h]
  have hsum : 0 ≤ (11/2 : ℝ) * (1) * (x/11 + y - 5/11)^2 + (27/11 : ℝ) * (1) * (x + 1/2)^2 + (1/2 : ℝ) * ((-5*x^2 - 4*x*y - 11*y^2 + 3)) * (1)^2 := by positivity
  have hid : ( 13 / 4  ) - (
  x * y - 2 * x + 5 * y ) = (11/2 : ℝ) * (1) * (x/11 + y - 5/11)^2 + (27/11 : ℝ) * (1) * (x + 1/2)^2 + (1/2 : ℝ) * ((-5*x^2 - 4*x*y - 11*y^2 + 3)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y : ℝ) (h : 5 * x ^ 2 + 4 * x * y + 11 * y ^ 2 = 3), x * y - 2 * x + 5 * y ≤ 13 / 4) := @solution
#print axioms solution
