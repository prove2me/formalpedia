-- Prove2me | solution 1 for WorkbookSource.base_14032
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:18:47.832462+00:00
-- url     : https://prove2.me/submissions/fb53fc36-07c9-4e08-b435-9c25d395493f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : -x * (1 + x) * (1 + z) * (x + y) * (y + z) - y * (1 + x) * (y + 1) * (y + z) * (z + x) - z * (1 + z) * (x + y) * (y + 1) * (z + x) + 1 / 2 * (1 + x) ^ 2 * (y + z) ^ 2 * (x + y) + 1 / 2 * (y + 1) ^ 2 * (z + x) ^ 2 * (y + z) + 1 / 2 * (1 + z) ^ 2 * (x + y) ^ 2 * (z + x) ≥ 0  := by
  have hw0 : 0 ≤ (x) := by linarith only [hx]
  have hw1 : 0 ≤ (y) := by linarith only [hy]
  have hw2 : 0 ≤ (z) := by linarith only [hz]
  have hsum : 0 ≤ (1/2 : ℝ) * ((z)) * (x*y - x*z - y + z)^2 + (1/2 : ℝ) * ((y)) * (x*z - x - y*z + y)^2 + (1/2 : ℝ) * ((x)) * (x*y - x - y*z + z)^2 := by positivity
  have hid : ( -x * (1 + x) * (1 + z) * (x + y) * (y + z) - y * (1 + x) * (y + 1) * (y + z) * (z + x) - z * (1 + z) * (x + y) * (y + 1) * (z + x) + 1 / 2 * (1 + x) ^ 2 * (y + z) ^ 2 * (x + y) + 1 / 2 * (y + 1) ^ 2 * (z + x) ^ 2 * (y + z) + 1 / 2 * (1 + z) ^ 2 * (x + y) ^ 2 * (z + x) ) - ( 0  ) = (1/2 : ℝ) * ((z)) * (x*y - x*z - y + z)^2 + (1/2 : ℝ) * ((y)) * (x*z - x - y*z + y)^2 + (1/2 : ℝ) * ((x)) * (x*y - x - y*z + z)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), -x * (1 + x) * (1 + z) * (x + y) * (y + z) - y * (1 + x) * (y + 1) * (y + z) * (z + x) - z * (1 + z) * (x + y) * (y + 1) * (z + x) + 1 / 2 * (1 + x) ^ 2 * (y + z) ^ 2 * (x + y) + 1 / 2 * (y + 1) ^ 2 * (z + x) ^ 2 * (y + z) + 1 / 2 * (1 + z) ^ 2 * (x + y) ^ 2 * (z + x) ≥ 0) := @solution
#print axioms solution
