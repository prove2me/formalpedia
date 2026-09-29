-- Prove2me | solution 1 for WorkbookSource.base_56296
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:18:48.486988+00:00
-- url     : https://prove2.me/submissions/f2474394-0f48-4313-b3d8-aac6e680bc71

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 2 + (1 / 3) * (x * y + y * z + z * x) ^ 2 ≥ x * y + y * z + z * x + 2 * x * y * z  := by
  have hw0 : 0 ≤ (x) := by linarith only [hx]
  have hw1 : 0 ≤ (y) := by linarith only [hy]
  have hw2 : 0 ≤ (z) := by linarith only [hz]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (-x*y/3 - x*z/3 - y*z/3 + 1)^2 + (1/9 : ℝ) * (1) * (-x*y/2 - x*z/2 + y*z)^2 + (1/12 : ℝ) * (1) * (-x*y + x*z)^2 + (1/3 : ℝ) * ((y) * (z)) * (1 - x)^2 + (1/3 : ℝ) * ((x) * (z)) * (1 - y)^2 + (1/3 : ℝ) * ((x) * (y)) * (1 - z)^2 := by positivity
  have hid : ( 2 + (1 / 3) * (x * y + y * z + z * x) ^ 2 ) - ( x * y + y * z + z * x + 2 * x * y * z  ) = (2 : ℝ) * (1) * (-x*y/3 - x*z/3 - y*z/3 + 1)^2 + (1/9 : ℝ) * (1) * (-x*y/2 - x*z/2 + y*z)^2 + (1/12 : ℝ) * (1) * (-x*y + x*z)^2 + (1/3 : ℝ) * ((y) * (z)) * (1 - x)^2 + (1/3 : ℝ) * ((x) * (z)) * (1 - y)^2 + (1/3 : ℝ) * ((x) * (y)) * (1 - z)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), 2 + (1 / 3) * (x * y + y * z + z * x) ^ 2 ≥ x * y + y * z + z * x + 2 * x * y * z) := @solution
#print axioms solution
