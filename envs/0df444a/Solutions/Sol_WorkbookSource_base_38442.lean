-- Prove2me | solution 1 for WorkbookSource.base_38442
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:56:43.992367+00:00
-- url     : https://prove2.me/submissions/0416c29f-2822-4c2f-955a-f3ba2704049a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z = 1) : 2 * (x ^ 2 + y ^ 2 + z ^ 2) + x + y + z ≥ 6 + x * y + y * z + x * z  := by
  have hw0 : 0 ≤ (x) := by linarith only [hx]
  have hw1 : 0 ≤ (y) := by linarith only [hy]
  have hw2 : 0 ≤ (z) := by linarith only [hz]
  have hw3 : 0 ≤ (x*y*z - 1) := by linarith only [h]
  have hw4 : 0 ≤ (-x*y*z + 1) := by linarith only [h]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (-x/2 - y/2 + z)^2 + (3/2 : ℝ) * (1) * (-x + y)^2 + (6 : ℝ) * ((x*y*z - 1)) * (1)^2 + (1 : ℝ) * ((z) * (-x*y*z + 1)) * (1)^2 + (1 : ℝ) * ((y) * (-x*y*z + 1)) * (1)^2 + (1 : ℝ) * ((y) * (z)) * (1 - x)^2 + (1 : ℝ) * ((x) * (-x*y*z + 1)) * (1)^2 + (1 : ℝ) * ((x) * (z)) * (1 - y)^2 + (1 : ℝ) * ((x) * (y)) * (1 - z)^2 := by positivity
  have hid : ( 2 * (x ^ 2 + y ^ 2 + z ^ 2) + x + y + z ) - ( 6 + x * y + y * z + x * z  ) = (2 : ℝ) * (1) * (-x/2 - y/2 + z)^2 + (3/2 : ℝ) * (1) * (-x + y)^2 + (6 : ℝ) * ((x*y*z - 1)) * (1)^2 + (1 : ℝ) * ((z) * (-x*y*z + 1)) * (1)^2 + (1 : ℝ) * ((y) * (-x*y*z + 1)) * (1)^2 + (1 : ℝ) * ((y) * (z)) * (1 - x)^2 + (1 : ℝ) * ((x) * (-x*y*z + 1)) * (1)^2 + (1 : ℝ) * ((x) * (z)) * (1 - y)^2 + (1 : ℝ) * ((x) * (y)) * (1 - z)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z = 1), 2 * (x ^ 2 + y ^ 2 + z ^ 2) + x + y + z ≥ 6 + x * y + y * z + x * z) := @solution
#print axioms solution
