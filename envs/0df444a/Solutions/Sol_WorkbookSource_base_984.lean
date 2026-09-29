-- Prove2me | solution 1 for WorkbookSource.base_984
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:45:53.301293+00:00
-- url     : https://prove2.me/submissions/054a2eed-49ea-47bf-8561-ac5c279b8e7b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + b + c = 1) :
  8 * a * b * c - 8 ≤ (a * b + b * c + c * a + 1)^2  := by
  have helim : c = (-a - b + 1) := by linarith only [h]
  have hsum : 0 ≤ (9 : ℝ) * (-2*a^2/9 - a*b/3 + a/9 - 2*b^2/9 + b/9 + 1)^2 + (26/9 : ℝ) * (11*a^2/26 + 6*a*b/13 - 5*a/13 - 7*b^2/26 + b)^2 + (32/13 : ℝ) * (-a^2/8 + 3*a*b/4 + a + 3*b^2/8)^2 := by positivity
  have hid : ( (a * b + b * c + c * a + 1)^2  ) - (
  8 * a * b * c - 8 ) = (9 : ℝ) * (-2*a^2/9 - a*b/3 + a/9 - 2*b^2/9 + b/9 + 1)^2 + (26/9 : ℝ) * (11*a^2/26 + 6*a*b/13 - 5*a/13 - 7*b^2/26 + b)^2 + (32/13 : ℝ) * (-a^2/8 + 3*a*b/4 + a + 3*b^2/8)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + b + c = 1), 8 * a * b * c - 8 ≤ (a * b + b * c + c * a + 1)^2) := @solution
#print axioms solution
