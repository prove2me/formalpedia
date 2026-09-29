-- Prove2me | solution 1 for WorkbookSource.plus_67937
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:14.690133+00:00
-- url     : https://prove2.me/submissions/eb9f6f7d-db11-412b-9f3b-9dae4867388c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a + b + c = 3) : (a * b + b * c + c * a - 3) ^ 2 ≥ 27 * (a * b * c - 1)   := by
  have helim : c = (-a - b + 3) := by linarith only [ha]
  have hsum : 0 ≤ (36 : ℝ) * (-a^2/12 - a*b/3 - a/4 - b^2/12 - b/4 + 1)^2 + (75/4 : ℝ) * (a^2/5 - a - b^2/5 + b)^2 := by positivity
  have hid : ( (a * b + b * c + c * a - 3) ^ 2 ) - ( 27 * (a * b * c - 1)   ) = (36 : ℝ) * (-a^2/12 - a*b/3 - a/4 - b^2/12 - b/4 + 1)^2 + (75/4 : ℝ) * (a^2/5 - a - b^2/5 + b)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a + b + c = 3), (a * b + b * c + c * a - 3) ^ 2 ≥ 27 * (a * b * c - 1)) := @solution
#print axioms solution
