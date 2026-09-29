-- Prove2me | solution 1 for WorkbookSource.plus_30461
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:12.562143+00:00
-- url     : https://prove2.me/submissions/470305be-d761-48bb-bb40-fa28c69084d0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a + b + c = 1) : 2 * (a^4 + b^4 + c^4) + a * b * c ≥ a^3 + b^3 + c^3   := by
  have helim : c = (-a - b + 1) := by linarith only [ha]
  have hsum : 0 ≤ (16 : ℝ) * (a^2/4 + a*b - 5*a/8 + b^2/4 - 5*b/8 + 1/4)^2 + (3 : ℝ) * (-a^2 + a/2 + b^2 - b/2)^2 := by positivity
  have hid : ( 2 * (a^4 + b^4 + c^4) + a * b * c ) - ( a^3 + b^3 + c^3   ) = (16 : ℝ) * (a^2/4 + a*b - 5*a/8 + b^2/4 - 5*b/8 + 1/4)^2 + (3 : ℝ) * (-a^2 + a/2 + b^2 - b/2)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a + b + c = 1), 2 * (a^4 + b^4 + c^4) + a * b * c ≥ a^3 + b^3 + c^3) := @solution
#print axioms solution
