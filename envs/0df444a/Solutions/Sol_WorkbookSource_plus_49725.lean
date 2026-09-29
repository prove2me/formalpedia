-- Prove2me | solution 1 for WorkbookSource.plus_49725
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:41:26.344021+00:00
-- url     : https://prove2.me/submissions/9e03b179-8f71-471e-861e-7b5dcad0c1d0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 = 6) :
  2 * a + 6 * b + 6 * c - 4 * b * c - 3 * c * a ≤ 19   := by
  have hw0 : 0 ≤ (a^2 + b^2 + c^2 - 6) := by linarith only [h]
  have hw1 : 0 ≤ (-a^2 - b^2 - c^2 + 6) := by linarith only [h]
  have hsum : 0 ≤ (4 : ℝ) * (1) * (-a/4 - 3*b/4 - 3*c/4 + 1)^2 + (9/4 : ℝ) * (1) * (a - b/3 + c/3)^2 + (5/2 : ℝ) * ((-a^2 - b^2 - c^2 + 6)) * (1)^2 := by positivity
  have hid : ( 19   ) - (
  2 * a + 6 * b + 6 * c - 4 * b * c - 3 * c * a ) = (4 : ℝ) * (1) * (-a/4 - 3*b/4 - 3*c/4 + 1)^2 + (9/4 : ℝ) * (1) * (a - b/3 + c/3)^2 + (5/2 : ℝ) * ((-a^2 - b^2 - c^2 + 6)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 = 6), 2 * a + 6 * b + 6 * c - 4 * b * c - 3 * c * a ≤ 19) := @solution
#print axioms solution
