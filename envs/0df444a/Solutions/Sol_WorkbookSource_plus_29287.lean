-- Prove2me | solution 1 for WorkbookSource.plus_29287
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:11.829968+00:00
-- url     : https://prove2.me/submissions/7a220542-68d7-454f-b253-dcfff0cd3b4a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a + b + c = 3) : a^4 + b^4 + c^4 + 3 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) + 3 ≥ 2 * (a * b * (a^2 + b^2) + b * c * (b^2 + c^2) + c * a * (c^2 + a^2)) + 6 * (a - b) * (a - c) * (b - c)   := by
  have helim : c = (-a - b + 3) := by linarith only [ha]
  have hsum : 0 ≤ (141 : ℝ) * (-11*a^2/47 - 17*a*b/47 + a - 2*b^2/47 + 22*b/47 - 36/47)^2 + (1791/47 : ℝ) * (18*a^2/199 - 79*a*b/199 - 95*b^2/199 + b - 18/199)^2 + (507/199 : ℝ) * (-8*a^2/13 + a*b - 2*b^2/13 + 8/13)^2 := by positivity
  have hid : ( a^4 + b^4 + c^4 + 3 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) + 3 ) - ( 2 * (a * b * (a^2 + b^2) + b * c * (b^2 + c^2) + c * a * (c^2 + a^2)) + 6 * (a - b) * (a - c) * (b - c)   ) = (141 : ℝ) * (-11*a^2/47 - 17*a*b/47 + a - 2*b^2/47 + 22*b/47 - 36/47)^2 + (1791/47 : ℝ) * (18*a^2/199 - 79*a*b/199 - 95*b^2/199 + b - 18/199)^2 + (507/199 : ℝ) * (-8*a^2/13 + a*b - 2*b^2/13 + 8/13)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a + b + c = 3), a^4 + b^4 + c^4 + 3 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) + 3 ≥ 2 * (a * b * (a^2 + b^2) + b * c * (b^2 + c^2) + c * a * (c^2 + a^2)) + 6 * (a - b) * (a - c) * (b - c)) := @solution
#print axioms solution
