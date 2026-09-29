-- Prove2me | solution 1 for WorkbookSource.base_19001
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:04.482203+00:00
-- url     : https://prove2.me/submissions/48dcc52c-3678-48e8-bce2-c1e4bdd41e6d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + b + c = 3) :
  3 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≥ a * b^2 + b * c^2 + c * a^2 + a * b + b * c + c * a  := by
  have helim : c = (-a - b + 3) := by linarith only [h]
  have hsum : 0 ≤ (13 : ℝ) * (a^2/13 - 5*a*b/13 + a/26 - 7*b^2/26 + b - 6/13)^2 + (363/52 : ℝ) * (-4*a^2/11 - 6*a*b/11 + a + b^2/11 - 2/11)^2 := by positivity
  have hid : (
  3 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ) - ( a * b^2 + b * c^2 + c * a^2 + a * b + b * c + c * a  ) = (13 : ℝ) * (a^2/13 - 5*a*b/13 + a/26 - 7*b^2/26 + b - 6/13)^2 + (363/52 : ℝ) * (-4*a^2/11 - 6*a*b/11 + a + b^2/11 - 2/11)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + b + c = 3), 3 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≥ a * b^2 + b * c^2 + c * a^2 + a * b + b * c + c * a) := @solution
#print axioms solution
