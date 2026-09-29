-- Prove2me | solution 1 for WorkbookSource.base_46041
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:08.864557+00:00
-- url     : https://prove2.me/submissions/187fa500-f064-4e72-8b1c-66f3049032d0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + b + c = 0) : (a * b + b * c + c * a) ^ 2 + 9 * a * b * c ≥ 3 * (a * b + b * c + c * a)  := by
  have helim : c = (-a - b) := by linarith only [h]
  have hsum : 0 ≤ (4 : ℝ) * (a^2/4 + a*b - 3*a/4 + b^2/4 - 3*b/4)^2 + (3/4 : ℝ) * (-a^2 - a + b^2 + b)^2 := by positivity
  have hid : ( (a * b + b * c + c * a) ^ 2 + 9 * a * b * c ) - ( 3 * (a * b + b * c + c * a)  ) = (4 : ℝ) * (a^2/4 + a*b - 3*a/4 + b^2/4 - 3*b/4)^2 + (3/4 : ℝ) * (-a^2 - a + b^2 + b)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + b + c = 0), (a * b + b * c + c * a) ^ 2 + 9 * a * b * c ≥ 3 * (a * b + b * c + c * a)) := @solution
#print axioms solution
