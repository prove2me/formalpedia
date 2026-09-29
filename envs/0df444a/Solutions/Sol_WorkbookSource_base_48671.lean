-- Prove2me | solution 1 for WorkbookSource.base_48671
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:24.83069+00:00
-- url     : https://prove2.me/submissions/4a6dc17c-8489-465c-9072-ca22b3475ee5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 12) :
  4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ≤ 48  := by
  have hw0 : 0 ≤ (a^2 + b^2 + c^2 + d^2 - 12) := by linarith only [h]
  have hw1 : 0 ≤ (-a^2 - b^2 - c^2 - d^2 + 12) := by linarith only [h]
  have hsum : 0 ≤ (4 : ℝ) * (1) * (-d^2/2 + d)^2 + (4 : ℝ) * (1) * (-c^2/2 + c)^2 + (4 : ℝ) * (1) * (-b^2/2 + b)^2 + (4 : ℝ) * (1) * (-a^2/2 + a)^2 + (4 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 12)) * (1)^2 := by positivity
  have hid : ( 48  ) - (
  4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ) = (4 : ℝ) * (1) * (-d^2/2 + d)^2 + (4 : ℝ) * (1) * (-c^2/2 + c)^2 + (4 : ℝ) * (1) * (-b^2/2 + b)^2 + (4 : ℝ) * (1) * (-a^2/2 + a)^2 + (4 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 12)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 12), 4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ≤ 48) := @solution
#print axioms solution
