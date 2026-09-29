-- Prove2me | solution 1 for WorkbookSource.base_17523
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:46:32.297265+00:00
-- url     : https://prove2.me/submissions/659ddb4c-6c02-4c5d-868a-af931c0ee598

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + b + c = 3) : a^2 * (6 * a^2 + 6 * c^2 - 3 * b^2 - 4) + b^2 * (6 * b^2 + 6 * c^2 - 3 * a^2 - 4) ≥ 0  := by
  have helim : c = (-a - b + 3) := by linarith only [h]
  have hsum : 0 ≤ (50 : ℝ) * (-3*a^2/25 - 6*a*b/25 - 9*b^2/25 + b)^2 + (50 : ℝ) * (-9*a^2/25 - 6*a*b/25 + a - 3*b^2/25)^2 + (24/5 : ℝ) * (-9*a^2/10 + a*b/20 + b^2)^2 + (114/125 : ℝ) * (a^2 + a*b/2)^2 := by positivity
  have hid : ( a^2 * (6 * a^2 + 6 * c^2 - 3 * b^2 - 4) + b^2 * (6 * b^2 + 6 * c^2 - 3 * a^2 - 4) ) - ( 0  ) = (50 : ℝ) * (-3*a^2/25 - 6*a*b/25 - 9*b^2/25 + b)^2 + (50 : ℝ) * (-9*a^2/25 - 6*a*b/25 + a - 3*b^2/25)^2 + (24/5 : ℝ) * (-9*a^2/10 + a*b/20 + b^2)^2 + (114/125 : ℝ) * (a^2 + a*b/2)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + b + c = 3), a^2 * (6 * a^2 + 6 * c^2 - 3 * b^2 - 4) + b^2 * (6 * b^2 + 6 * c^2 - 3 * a^2 - 4) ≥ 0) := @solution
#print axioms solution
