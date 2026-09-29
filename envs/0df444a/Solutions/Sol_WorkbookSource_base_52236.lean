-- Prove2me | solution 1 for WorkbookSource.base_52236
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:21.368726+00:00
-- url     : https://prove2.me/submissions/08d935bd-248f-4bb4-b3b5-caa32546d0e6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x^2 + y^2 + z^2 = 3) :  x^3 + y^3 + z^3 + 3 * (x + y + z) ≥ 9 + 3 * x * y * z  := by
  have hw0 : 0 ≤ (x) := by linarith only [hx]
  have hw1 : 0 ≤ (y) := by linarith only [hy]
  have hw2 : 0 ≤ (z) := by linarith only [hz]
  have hw3 : 0 ≤ (x^2 + y^2 + z^2 - 3) := by linarith only [h]
  have hw4 : 0 ≤ (-x^2 - y^2 - z^2 + 3) := by linarith only [h]
  have hsum : 0 ≤ (3 : ℝ) * ((x^2 + y^2 + z^2 - 3)) * (1)^2 + (3/2 : ℝ) * ((z)) * (1 - z)^2 + (1/2 : ℝ) * ((z)) * (-x + y)^2 + (1/2 : ℝ) * ((z) * (-x^2 - y^2 - z^2 + 3)) * (1)^2 + (3/2 : ℝ) * ((y)) * (1 - y)^2 + (1/2 : ℝ) * ((y)) * (-x + z)^2 + (1/2 : ℝ) * ((y) * (-x^2 - y^2 - z^2 + 3)) * (1)^2 + (3/2 : ℝ) * ((x)) * (1 - x)^2 + (1/2 : ℝ) * ((x)) * (-y + z)^2 + (1/2 : ℝ) * ((x) * (-x^2 - y^2 - z^2 + 3)) * (1)^2 := by positivity
  have hid : (  x^3 + y^3 + z^3 + 3 * (x + y + z) ) - ( 9 + 3 * x * y * z  ) = (3 : ℝ) * ((x^2 + y^2 + z^2 - 3)) * (1)^2 + (3/2 : ℝ) * ((z)) * (1 - z)^2 + (1/2 : ℝ) * ((z)) * (-x + y)^2 + (1/2 : ℝ) * ((z) * (-x^2 - y^2 - z^2 + 3)) * (1)^2 + (3/2 : ℝ) * ((y)) * (1 - y)^2 + (1/2 : ℝ) * ((y)) * (-x + z)^2 + (1/2 : ℝ) * ((y) * (-x^2 - y^2 - z^2 + 3)) * (1)^2 + (3/2 : ℝ) * ((x)) * (1 - x)^2 + (1/2 : ℝ) * ((x)) * (-y + z)^2 + (1/2 : ℝ) * ((x) * (-x^2 - y^2 - z^2 + 3)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x^2 + y^2 + z^2 = 3), x^3 + y^3 + z^3 + 3 * (x + y + z) ≥ 9 + 3 * x * y * z) := @solution
#print axioms solution
