-- Prove2me | solution 1 for WorkbookSource.base_7985
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:46:28.60754+00:00
-- url     : https://prove2.me/submissions/007dcec1-f0fd-45a7-8e5c-58564b8848ac

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + b + c = 3) :
  a^3 * b + b^3 * c + c^3 * a + 6 * a * b * c ≤ 9  := by
  have helim : c = (-a - b + 3) := by linarith only [h]
  have hsum : 0 ≤ (21 : ℝ) * (-3*a^2/14 - 2*a*b/7 + a + b^2/14 + b/14 - 9/14)^2 + (81/28 : ℝ) * (a^2/9 - 8*a*b/9 - 5*b^2/9 + b + 1/3)^2 := by positivity
  have hid : ( 9  ) - (
  a^3 * b + b^3 * c + c^3 * a + 6 * a * b * c ) = (21 : ℝ) * (-3*a^2/14 - 2*a*b/7 + a + b^2/14 + b/14 - 9/14)^2 + (81/28 : ℝ) * (a^2/9 - 8*a*b/9 - 5*b^2/9 + b + 1/3)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + b + c = 3), a^3 * b + b^3 * c + c^3 * a + 6 * a * b * c ≤ 9) := @solution
#print axioms solution
