-- Prove2me | solution 1 for WorkbookSource.base_1812
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:45:53.917979+00:00
-- url     : https://prove2.me/submissions/62392571-c40d-469a-a572-9e8d30ae1ee6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + b + c = 3) : a^4 + b^4 + c^4 + 4 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ 5 * (a^2 + b^2 + c^2)  := by
  have helim : c = (-a - b + 3) := by linarith only [h]
  have hsum : 0 ≤ (56 : ℝ) * (-a^2/7 - 11*a*b/28 + 31*a/56 - 9*b^2/28 + b - 39/56)^2 + (2175/56 : ℝ) * (-152*a^2/435 - 22*a*b/87 + a + 22*b^2/435 - 13/29)^2 + (250/87 : ℝ) * (-a^2/5 + a*b - b^2/5 - 3/5)^2 := by positivity
  have hid : ( a^4 + b^4 + c^4 + 4 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ) - ( 5 * (a^2 + b^2 + c^2)  ) = (56 : ℝ) * (-a^2/7 - 11*a*b/28 + 31*a/56 - 9*b^2/28 + b - 39/56)^2 + (2175/56 : ℝ) * (-152*a^2/435 - 22*a*b/87 + a + 22*b^2/435 - 13/29)^2 + (250/87 : ℝ) * (-a^2/5 + a*b - b^2/5 - 3/5)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + b + c = 3), a^4 + b^4 + c^4 + 4 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ 5 * (a^2 + b^2 + c^2)) := @solution
#print axioms solution
