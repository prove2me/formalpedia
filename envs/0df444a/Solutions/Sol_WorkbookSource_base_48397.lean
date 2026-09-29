-- Prove2me | solution 1 for WorkbookSource.base_48397
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:24.216926+00:00
-- url     : https://prove2.me/submissions/40fa5879-58d5-4f22-bddf-f87152988099

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z t : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2 = 4) :
  x * y * z * t ≤ 1  := by
  have hw0 : 0 ≤ (t^2 + x^2 + y^2 + z^2 - 4) := by linarith only [h]
  have hw1 : 0 ≤ (-t^2 - x^2 - y^2 - z^2 + 4) := by linarith only [h]
  have hsum : 0 ≤ (1/6 : ℝ) * (1) * (t*z - x*y)^2 + (1/6 : ℝ) * (1) * (t*y - x*z)^2 + (1/6 : ℝ) * (1) * (-t*x + y*z)^2 + (1/16 : ℝ) * (1) * (t^2 - x^2/3 - y^2/3 - z^2/3)^2 + (1/18 : ℝ) * (1) * (-x^2/2 - y^2/2 + z^2)^2 + (1/24 : ℝ) * (1) * (-x^2 + y^2)^2 + (1/4 : ℝ) * ((-t^2 - x^2 - y^2 - z^2 + 4)) * (1)^2 + (1/16 : ℝ) * ((-t^2 - x^2 - y^2 - z^2 + 4)) * (t)^2 + (1/16 : ℝ) * ((-t^2 - x^2 - y^2 - z^2 + 4)) * (z)^2 + (1/16 : ℝ) * ((-t^2 - x^2 - y^2 - z^2 + 4)) * (y)^2 + (1/16 : ℝ) * ((-t^2 - x^2 - y^2 - z^2 + 4)) * (x)^2 := by positivity
  have hid : ( 1  ) - (
  x * y * z * t ) = (1/6 : ℝ) * (1) * (t*z - x*y)^2 + (1/6 : ℝ) * (1) * (t*y - x*z)^2 + (1/6 : ℝ) * (1) * (-t*x + y*z)^2 + (1/16 : ℝ) * (1) * (t^2 - x^2/3 - y^2/3 - z^2/3)^2 + (1/18 : ℝ) * (1) * (-x^2/2 - y^2/2 + z^2)^2 + (1/24 : ℝ) * (1) * (-x^2 + y^2)^2 + (1/4 : ℝ) * ((-t^2 - x^2 - y^2 - z^2 + 4)) * (1)^2 + (1/16 : ℝ) * ((-t^2 - x^2 - y^2 - z^2 + 4)) * (t)^2 + (1/16 : ℝ) * ((-t^2 - x^2 - y^2 - z^2 + 4)) * (z)^2 + (1/16 : ℝ) * ((-t^2 - x^2 - y^2 - z^2 + 4)) * (y)^2 + (1/16 : ℝ) * ((-t^2 - x^2 - y^2 - z^2 + 4)) * (x)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z t : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2 = 4), x * y * z * t ≤ 1) := @solution
#print axioms solution
