-- Prove2me | solution 1 for WorkbookSource.base_19519
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:45:13.408189+00:00
-- url     : https://prove2.me/submissions/eaaa9a21-ab76-4545-8f6a-98769be31fd2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (habc : x * y * z = 1) : 
  x^3 * y + y^3 * z + z^3 * x ≥ x * y + z * x + y * z  := by
  have hw0 : 0 ≤ (x) := by linarith only [hx]
  have hw1 : 0 ≤ (y) := by linarith only [hy]
  have hw2 : 0 ≤ (z) := by linarith only [hz]
  have hw3 : 0 ≤ (x*y*z - 1) := by linarith only [habc]
  have hw4 : 0 ≤ (-x*y*z + 1) := by linarith only [habc]
  have hsum : 0 ≤ (2/3 : ℝ) * ((z)) * (1 - y)^2 + (2/3 : ℝ) * ((z) * (x*y*z - 1)) * (1)^2 + (2/3 : ℝ) * ((y)) * (1 - x)^2 + (2/3 : ℝ) * ((y) * (x*y*z - 1)) * (1)^2 + (1 : ℝ) * ((y) * (z)) * (-2*x/3 + y - 1/3)^2 + (2/9 : ℝ) * ((y) * (z)) * (1 - x)^2 + (2/3 : ℝ) * ((x)) * (1 - z)^2 + (2/3 : ℝ) * ((x) * (x*y*z - 1)) * (1)^2 + (1 : ℝ) * ((x) * (z)) * (-2*y/3 + z - 1/3)^2 + (2/9 : ℝ) * ((x) * (z)) * (1 - y)^2 + (1 : ℝ) * ((x) * (y)) * (x - 2*z/3 - 1/3)^2 + (2/9 : ℝ) * ((x) * (y)) * (1 - z)^2 := by positivity
  have hid : ( 
  x^3 * y + y^3 * z + z^3 * x ) - ( x * y + z * x + y * z  ) = (2/3 : ℝ) * ((z)) * (1 - y)^2 + (2/3 : ℝ) * ((z) * (x*y*z - 1)) * (1)^2 + (2/3 : ℝ) * ((y)) * (1 - x)^2 + (2/3 : ℝ) * ((y) * (x*y*z - 1)) * (1)^2 + (1 : ℝ) * ((y) * (z)) * (-2*x/3 + y - 1/3)^2 + (2/9 : ℝ) * ((y) * (z)) * (1 - x)^2 + (2/3 : ℝ) * ((x)) * (1 - z)^2 + (2/3 : ℝ) * ((x) * (x*y*z - 1)) * (1)^2 + (1 : ℝ) * ((x) * (z)) * (-2*y/3 + z - 1/3)^2 + (2/9 : ℝ) * ((x) * (z)) * (1 - y)^2 + (1 : ℝ) * ((x) * (y)) * (x - 2*z/3 - 1/3)^2 + (2/9 : ℝ) * ((x) * (y)) * (1 - z)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (habc : x * y * z = 1), x^3 * y + y^3 * z + z^3 * x ≥ x * y + z * x + y * z) := @solution
#print axioms solution
