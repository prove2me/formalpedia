-- Prove2me | solution 1 for WorkbookSource.plus_66952
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:20:10.560181+00:00
-- url     : https://prove2.me/submissions/16574c16-83a8-4f8d-bd38-2abaff748f38

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x * y * (x ^ 2 + y ^ 2) + y * z * (y ^ 2 + z ^ 2) + z * x * (z ^ 2 + x ^ 2)) ≤ (1 / 8) * (x + y + z) ^ 4   := by
  have hw0 : 0 ≤ (x) := by linarith only [hx]
  have hw1 : 0 ≤ (y) := by linarith only [hy]
  have hw2 : 0 ≤ (z) := by linarith only [hz]
  have hsum : 0 ≤ (1/2 : ℝ) * (1) * (-x^2/2 + x*y + x*z - y^2/2 + y*z - z^2/2)^2 + (1 : ℝ) * ((y) * (z)) * (x)^2 + (1 : ℝ) * ((x) * (z)) * (y)^2 + (1 : ℝ) * ((x) * (y)) * (z)^2 := by positivity
  have hid : ( (1 / 8) * (x + y + z) ^ 4   ) - ( (x * y * (x ^ 2 + y ^ 2) + y * z * (y ^ 2 + z ^ 2) + z * x * (z ^ 2 + x ^ 2)) ) = (1/2 : ℝ) * (1) * (-x^2/2 + x*y + x*z - y^2/2 + y*z - z^2/2)^2 + (1 : ℝ) * ((y) * (z)) * (x)^2 + (1 : ℝ) * ((x) * (z)) * (y)^2 + (1 : ℝ) * ((x) * (y)) * (z)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), (x * y * (x ^ 2 + y ^ 2) + y * z * (y ^ 2 + z ^ 2) + z * x * (z ^ 2 + x ^ 2)) ≤ (1 / 8) * (x + y + z) ^ 4) := @solution
#print axioms solution
