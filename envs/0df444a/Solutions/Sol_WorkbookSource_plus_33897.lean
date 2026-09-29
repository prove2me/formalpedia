-- Prove2me | solution 1 for WorkbookSource.plus_33897
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:13.247375+00:00
-- url     : https://prove2.me/submissions/ecbb4967-adec-4fd2-897b-3daf65a951d6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (h : a + 2 * b + 3 * c + 4 * d = 10) :
  a^2 + b^2 + c^2 + d^2 + a * b + a * c + a * d + b * c + b * d + c * d ≥ 5   := by
  have helim : a = (-2*b - 3*c - 4*d + 10) := by linarith only [h]
  have hsum : 0 ≤ (95 : ℝ) * (-3*b/19 - 5*c/19 - 7*d/19 + 1)^2 + (12/19 : ℝ) * (b + c/12 - d/24)^2 + (5/12 : ℝ) * (c - d/2)^2 := by positivity
  have hid : (
  a^2 + b^2 + c^2 + d^2 + a * b + a * c + a * d + b * c + b * d + c * d ) - ( 5   ) = (95 : ℝ) * (-3*b/19 - 5*c/19 - 7*d/19 + 1)^2 + (12/19 : ℝ) * (b + c/12 - d/24)^2 + (5/12 : ℝ) * (c - d/2)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (h : a + 2 * b + 3 * c + 4 * d = 10), a^2 + b^2 + c^2 + d^2 + a * b + a * c + a * d + b * c + b * d + c * d ≥ 5) := @solution
#print axioms solution
