-- Prove2me | solution 1 for WorkbookSource.base_38274
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:14:30.143842+00:00
-- url     : https://prove2.me/submissions/534234f5-7206-4b72-8ef9-b931eaa39729

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x^2 + y^2 + z^2 = 2) :
  (x + y + z + 2) * (x * y + y * z + z * x) - 9 * x * y * z ≤ 4  := by
  have hw0 : 0 ≤ (x) := by linarith only [hx]
  have hw1 : 0 ≤ (y) := by linarith only [hy]
  have hw2 : 0 ≤ (z) := by linarith only [hz]
  have hw3 : 0 ≤ (x^2 + y^2 + z^2 - 2) := by linarith only [h]
  have hw4 : 0 ≤ (-x^2 - y^2 - z^2 + 2) := by linarith only [h]
  have hsum : 0 ≤ (3/2 : ℝ) * (1) * (x^2/3 - x*y/2 - x*z/2 + 2*x/3 - y^2/6 + y*z - y/3 - z^2/6 - z/3)^2 + (9/8 : ℝ) * (1) * (-x*y + x*z + y^2/3 + 2*y/3 - z^2/3 - 2*z/3)^2 + (1/3 : ℝ) * (1) * (x^2/2 - x/2 + y^2/2 - y/2 - z^2 + z)^2 + (1/4 : ℝ) * (1) * (x^2 - x - y^2 + y)^2 + (2 : ℝ) * ((-x^2 - y^2 - z^2 + 2)) * (1)^2 + (1/2 : ℝ) * ((-x^2 - y^2 - z^2 + 2)) * (-x/2 - y/2 + z)^2 + (3/8 : ℝ) * ((-x^2 - y^2 - z^2 + 2)) * (-x + y)^2 := by positivity
  have hid : ( 4  ) - (
  (x + y + z + 2) * (x * y + y * z + z * x) - 9 * x * y * z ) = (3/2 : ℝ) * (1) * (x^2/3 - x*y/2 - x*z/2 + 2*x/3 - y^2/6 + y*z - y/3 - z^2/6 - z/3)^2 + (9/8 : ℝ) * (1) * (-x*y + x*z + y^2/3 + 2*y/3 - z^2/3 - 2*z/3)^2 + (1/3 : ℝ) * (1) * (x^2/2 - x/2 + y^2/2 - y/2 - z^2 + z)^2 + (1/4 : ℝ) * (1) * (x^2 - x - y^2 + y)^2 + (2 : ℝ) * ((-x^2 - y^2 - z^2 + 2)) * (1)^2 + (1/2 : ℝ) * ((-x^2 - y^2 - z^2 + 2)) * (-x/2 - y/2 + z)^2 + (3/8 : ℝ) * ((-x^2 - y^2 - z^2 + 2)) * (-x + y)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x^2 + y^2 + z^2 = 2), (x + y + z + 2) * (x * y + y * z + z * x) - 9 * x * y * z ≤ 4) := @solution
#print axioms solution
