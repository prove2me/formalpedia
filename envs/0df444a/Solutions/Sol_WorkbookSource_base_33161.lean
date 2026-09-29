-- Prove2me | solution 1 for WorkbookSource.base_33161
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:41:03.348156+00:00
-- url     : https://prove2.me/submissions/724bd779-1b60-4cb0-a3ce-51999bbab3d0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (hab : a * b + b * c + c * a = 0) : a^2 * (1 - b) + b^2 * (1 - c) + c^2 * (1 - a) ≥ a * b * c * (a + b + c - 3)  := by
  have hw0 : 0 ≤ (a*b + a*c + b*c) := by linarith only [hab]
  have hw1 : 0 ≤ (-a*b - a*c - b*c) := by linarith only [hab]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (a*b/2 - a*c/2 - a/2 - b/2 + c)^2 + (3/4 : ℝ) * (1) * (a*b/3 + a*c/3 - a - 2*b*c/3 + b)^2 + (1 : ℝ) * ((a*b + a*c + b*c)) * (1)^2 + (1/3 : ℝ) * ((a*b + a*c + b*c) * (-a*b - a*c - b*c)) * (1)^2 := by positivity
  have hid : ( a^2 * (1 - b) + b^2 * (1 - c) + c^2 * (1 - a) ) - ( a * b * c * (a + b + c - 3)  ) = (1 : ℝ) * (1) * (a*b/2 - a*c/2 - a/2 - b/2 + c)^2 + (3/4 : ℝ) * (1) * (a*b/3 + a*c/3 - a - 2*b*c/3 + b)^2 + (1 : ℝ) * ((a*b + a*c + b*c)) * (1)^2 + (1/3 : ℝ) * ((a*b + a*c + b*c) * (-a*b - a*c - b*c)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (hab : a * b + b * c + c * a = 0), a^2 * (1 - b) + b^2 * (1 - c) + c^2 * (1 - a) ≥ a * b * c * (a + b + c - 3)) := @solution
#print axioms solution
