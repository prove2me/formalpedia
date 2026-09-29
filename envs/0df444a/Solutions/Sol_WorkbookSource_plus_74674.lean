-- Prove2me | solution 1 for WorkbookSource.plus_74674
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:15.359341+00:00
-- url     : https://prove2.me/submissions/d5e33679-c95a-4a5a-a82b-0cb6b998258c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (hab : a + b + c = 3) : (a * b + b * c + c * a) ^ 2 + 9 ≥ 18 * a * b * c   := by
  have helim : c = (-a - b + 3) := by linarith only [hab]
  have hsum : 0 ≤ (12 : ℝ) * (a^2/4 - a - b^2/4 + b)^2 + (9 : ℝ) * (-a^2/6 - 2*a*b/3 - b^2/6 + 1)^2 := by positivity
  have hid : ( (a * b + b * c + c * a) ^ 2 + 9 ) - ( 18 * a * b * c   ) = (12 : ℝ) * (a^2/4 - a - b^2/4 + b)^2 + (9 : ℝ) * (-a^2/6 - 2*a*b/3 - b^2/6 + 1)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (hab : a + b + c = 3), (a * b + b * c + c * a) ^ 2 + 9 ≥ 18 * a * b * c) := @solution
#print axioms solution
