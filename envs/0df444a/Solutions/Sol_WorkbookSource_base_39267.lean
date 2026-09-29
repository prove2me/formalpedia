-- Prove2me | solution 1 for WorkbookSource.base_39267
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:41:04.128063+00:00
-- url     : https://prove2.me/submissions/d2cc031c-1d5b-462f-8219-0e4bd0016abe

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (h : x * y + y * z + z * x = 5) :
  3 * x ^ 2 + 3 * y ^ 2 + z ^ 2 ≥ 10  := by
  have hw0 : 0 ≤ (x*y + x*z + y*z - 5) := by linarith only [h]
  have hw1 : 0 ≤ (-x*y - x*z - y*z + 5) := by linarith only [h]
  have hsum : 0 ≤ (3 : ℝ) * (1) * (-x/3 + y - z/3)^2 + (8/3 : ℝ) * (1) * (x - z/2)^2 + (2 : ℝ) * ((x*y + x*z + y*z - 5)) * (1)^2 := by positivity
  have hid : (
  3 * x ^ 2 + 3 * y ^ 2 + z ^ 2 ) - ( 10  ) = (3 : ℝ) * (1) * (-x/3 + y - z/3)^2 + (8/3 : ℝ) * (1) * (x - z/2)^2 + (2 : ℝ) * ((x*y + x*z + y*z - 5)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (h : x * y + y * z + z * x = 5), 3 * x ^ 2 + 3 * y ^ 2 + z ^ 2 ≥ 10) := @solution
#print axioms solution
