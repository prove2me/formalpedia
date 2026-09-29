-- Prove2me | solution 1 for WorkbookSource.base_42167
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:08.188157+00:00
-- url     : https://prove2.me/submissions/42ed4564-ab3c-420a-a648-b29e4e64c4d5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + 2 * b + 3 * c = 10) : a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a ≥ 10  := by
  have helim : a = (-2*b - 3*c + 10) := by linarith only [h]
  have hsum : 0 ≤ (90 : ℝ) * (-b/6 - 5*c/18 + 1)^2 + (1/2 : ℝ) * (b - c/3)^2 := by positivity
  have hid : ( a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a ) - ( 10  ) = (90 : ℝ) * (-b/6 - 5*c/18 + 1)^2 + (1/2 : ℝ) * (b - c/3)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + 2 * b + 3 * c = 10), a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a ≥ 10) := @solution
#print axioms solution
