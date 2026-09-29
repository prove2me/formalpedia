-- Prove2me | solution 1 for WorkbookSource.base_903
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:45:52.711699+00:00
-- url     : https://prove2.me/submissions/33043376-2fdb-4f42-aa4c-de6f4ecd297b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + b + c = 5) :
  a^4 + b^4 + c^4 + 13 * (a^2 + b^2 + c^2) ≥ 6 * (a^3 + b^3 + c^3) + 48  := by
  have helim : c = (-a - b + 5) := by linarith only [h]
  have hsum : 0 ≤ (152 : ℝ) * (7*a^2/76 + 3*a*b/19 - 45*a/76 + 7*b^2/76 - 45*b/76 + 1)^2 + (179/38 : ℝ) * (49*a^2/179 + 8*a*b/179 - 163*a/179 - 65*b^2/179 + b)^2 + (144/179 : ℝ) * (-2*a^2/3 + a*b/2 + a - b^2/3)^2 := by positivity
  have hid : (
  a^4 + b^4 + c^4 + 13 * (a^2 + b^2 + c^2) ) - ( 6 * (a^3 + b^3 + c^3) + 48  ) = (152 : ℝ) * (7*a^2/76 + 3*a*b/19 - 45*a/76 + 7*b^2/76 - 45*b/76 + 1)^2 + (179/38 : ℝ) * (49*a^2/179 + 8*a*b/179 - 163*a/179 - 65*b^2/179 + b)^2 + (144/179 : ℝ) * (-2*a^2/3 + a*b/2 + a - b^2/3)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + b + c = 5), a^4 + b^4 + c^4 + 13 * (a^2 + b^2 + c^2) ≥ 6 * (a^3 + b^3 + c^3) + 48) := @solution
#print axioms solution
