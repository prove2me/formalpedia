-- Prove2me | solution 1 for WorkbookSource.base_23467
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:05.251199+00:00
-- url     : https://prove2.me/submissions/196766fb-53bf-4e1a-b880-9d7a88668b1c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution  (a b c: ℝ)
  (h₀ : a + b + c = 2) :
  2 ≥ (a^2 + b^2 + c^2) * (a * b + b * c + c * a)  := by
  have helim : c = (-a - b + 2) := by linarith only [h₀]
  have hsum : 0 ≤ (8 : ℝ) * (-a^2/2 - a*b/2 + a - b^2/2 + b - 1/2)^2 := by positivity
  have hid : (
  2 ) - ( (a^2 + b^2 + c^2) * (a * b + b * c + c * a)  ) = (8 : ℝ) * (-a^2/2 - a*b/2 + a - b^2/2 + b - 1/2)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c: ℝ)
  (h₀ : a + b + c = 2), 2 ≥ (a^2 + b^2 + c^2) * (a * b + b * c + c * a)) := @solution
#print axioms solution
