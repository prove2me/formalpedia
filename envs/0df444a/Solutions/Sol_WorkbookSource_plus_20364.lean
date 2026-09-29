-- Prove2me | solution 1 for WorkbookSource.plus_20364
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:53:09.690481+00:00
-- url     : https://prove2.me/submissions/79fca948-6fa7-449b-94bf-b16df8c0199e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x^2 + y^2 + z^2 + 2 * x * y * z = 1) : (x + y + z) - (x * y + y * z + z * x) ≥ 3 / 4   := by
  have hw0 : 0 ≤ (x) := by linarith only [hx]
  have hw1 : 0 ≤ (y) := by linarith only [hy]
  have hw2 : 0 ≤ (z) := by linarith only [hz]
  have hw3 : 0 ≤ (x^2 + 2*x*y*z + y^2 + z^2 - 1) := by linarith only [h]
  have hw4 : 0 ≤ (-x^2 - 2*x*y*z - y^2 - z^2 + 1) := by linarith only [h]
  have hsum : 0 ≤ (3/4 : ℝ) * ((x^2 + 2*x*y*z + y^2 + z^2 - 1)) * (1)^2 + (1/2 : ℝ) * ((z)) * (-5*x/8 - 5*y/8 - 3*z/4 + 1)^2 + (7/32 : ℝ) * ((z)) * (-x/2 - y/2 + z)^2 + (1/2 : ℝ) * ((z) * (-x^2 - 2*x*y*z - y^2 - z^2 + 1)) * (1)^2 + (1/2 : ℝ) * ((y)) * (-5*x/8 - 3*y/4 - 5*z/8 + 1)^2 + (7/32 : ℝ) * ((y)) * (-x/2 + y - z/2)^2 + (1/2 : ℝ) * ((y) * (-x^2 - 2*x*y*z - y^2 - z^2 + 1)) * (1)^2 + (1 : ℝ) * ((y) * (z)) * (x - 1/2)^2 + (1/2 : ℝ) * ((x)) * (-3*x/4 - 5*y/8 - 5*z/8 + 1)^2 + (7/32 : ℝ) * ((x)) * (x - y/2 - z/2)^2 + (1/2 : ℝ) * ((x) * (-x^2 - 2*x*y*z - y^2 - z^2 + 1)) * (1)^2 + (1 : ℝ) * ((x) * (z)) * (y - 1/2)^2 + (1 : ℝ) * ((x) * (y)) * (z - 1/2)^2 := by positivity
  have hid : ( (x + y + z) - (x * y + y * z + z * x) ) - ( 3 / 4   ) = (3/4 : ℝ) * ((x^2 + 2*x*y*z + y^2 + z^2 - 1)) * (1)^2 + (1/2 : ℝ) * ((z)) * (-5*x/8 - 5*y/8 - 3*z/4 + 1)^2 + (7/32 : ℝ) * ((z)) * (-x/2 - y/2 + z)^2 + (1/2 : ℝ) * ((z) * (-x^2 - 2*x*y*z - y^2 - z^2 + 1)) * (1)^2 + (1/2 : ℝ) * ((y)) * (-5*x/8 - 3*y/4 - 5*z/8 + 1)^2 + (7/32 : ℝ) * ((y)) * (-x/2 + y - z/2)^2 + (1/2 : ℝ) * ((y) * (-x^2 - 2*x*y*z - y^2 - z^2 + 1)) * (1)^2 + (1 : ℝ) * ((y) * (z)) * (x - 1/2)^2 + (1/2 : ℝ) * ((x)) * (-3*x/4 - 5*y/8 - 5*z/8 + 1)^2 + (7/32 : ℝ) * ((x)) * (x - y/2 - z/2)^2 + (1/2 : ℝ) * ((x) * (-x^2 - 2*x*y*z - y^2 - z^2 + 1)) * (1)^2 + (1 : ℝ) * ((x) * (z)) * (y - 1/2)^2 + (1 : ℝ) * ((x) * (y)) * (z - 1/2)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x^2 + y^2 + z^2 + 2 * x * y * z = 1), (x + y + z) - (x * y + y * z + z * x) ≥ 3 / 4) := @solution
#print axioms solution
