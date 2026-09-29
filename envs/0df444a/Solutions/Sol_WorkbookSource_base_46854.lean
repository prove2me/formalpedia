-- Prove2me | solution 1 for WorkbookSource.base_46854
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:40:06.949073+00:00
-- url     : https://prove2.me/submissions/8f8d06f0-b2b9-422a-ba33-16ae0a6abf7f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (h : 9 * a ^ 2 + 8 * a * b + 7 * b ^ 2 ≤ 6) :
 7 * a + 5 * b + 12 * a * b ≤ 9  := by
  have hw0 : 0 ≤ (-9*a^2 - 8*a*b - 7*b^2 + 6) := by linarith only [h]
  have hsum : 0 ≤ (9 : ℝ) * (1) * (a - 2*b/9 - 7/18)^2 + (59/9 : ℝ) * (1) * (b - 1/2)^2 + (1 : ℝ) * ((-9*a^2 - 8*a*b - 7*b^2 + 6)) * (1)^2 := by positivity
  have hid : ( 9  ) - (
 7 * a + 5 * b + 12 * a * b ) = (9 : ℝ) * (1) * (a - 2*b/9 - 7/18)^2 + (59/9 : ℝ) * (1) * (b - 1/2)^2 + (1 : ℝ) * ((-9*a^2 - 8*a*b - 7*b^2 + 6)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (h : 9 * a ^ 2 + 8 * a * b + 7 * b ^ 2 ≤ 6), 7 * a + 5 * b + 12 * a * b ≤ 9) := @solution
#print axioms solution
