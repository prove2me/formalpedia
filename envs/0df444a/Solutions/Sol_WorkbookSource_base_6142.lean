-- Prove2me | solution 1 for WorkbookSource.base_6142
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:43:30.926855+00:00
-- url     : https://prove2.me/submissions/dfc4902c-ce0f-4a1d-9e4a-cd49f7cb38b6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (h : 1 ≥ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) :
  6 ≥ (a + b) ^ 4 + (a + c) ^ 4 + (a + d) ^ 4 + (b + c) ^ 4 + (b + d) ^ 4 + (c + d) ^ 4  := by
  have hw0 : 0 ≤ (-a^2 - b^2 - c^2 - d^2 + 1) := by linarith only [h]
  have hsum : 0 ≤ (9/4 : ℝ) * (1) * (-2*a*b/3 - 2*a*c/3 - 2*a*d/3 - 2*b*c/3 - 2*b*d/3 - 2*c*d/3 + 1)^2 + (1 : ℝ) * (1) * (a^2/2 - a*b + b^2/2 - c^2/2 + c*d - d^2/2)^2 + (1 : ℝ) * (1) * (a^2/2 - a*c - b^2/2 + b*d + c^2/2 - d^2/2)^2 + (1 : ℝ) * (1) * (a^2/2 - a*d - b^2/2 + b*c - c^2/2 + d^2/2)^2 + (15/4 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1)) * (1)^2 + (15/4 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1)) * (2*a/5 + 2*b/5 + 2*c/5 + d)^2 + (63/20 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1)) * (2*a/7 + 2*b/7 + c)^2 + (81/28 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1)) * (2*a/9 + b)^2 + (11/4 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1)) * (a)^2 := by positivity
  have hid : (
  6 ) - ( (a + b) ^ 4 + (a + c) ^ 4 + (a + d) ^ 4 + (b + c) ^ 4 + (b + d) ^ 4 + (c + d) ^ 4  ) = (9/4 : ℝ) * (1) * (-2*a*b/3 - 2*a*c/3 - 2*a*d/3 - 2*b*c/3 - 2*b*d/3 - 2*c*d/3 + 1)^2 + (1 : ℝ) * (1) * (a^2/2 - a*b + b^2/2 - c^2/2 + c*d - d^2/2)^2 + (1 : ℝ) * (1) * (a^2/2 - a*c - b^2/2 + b*d + c^2/2 - d^2/2)^2 + (1 : ℝ) * (1) * (a^2/2 - a*d - b^2/2 + b*c - c^2/2 + d^2/2)^2 + (15/4 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1)) * (1)^2 + (15/4 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1)) * (2*a/5 + 2*b/5 + 2*c/5 + d)^2 + (63/20 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1)) * (2*a/7 + 2*b/7 + c)^2 + (81/28 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1)) * (2*a/9 + b)^2 + (11/4 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1)) * (a)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (h : 1 ≥ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2), 6 ≥ (a + b) ^ 4 + (a + c) ^ 4 + (a + d) ^ 4 + (b + c) ^ 4 + (b + d) ^ 4 + (c + d) ^ 4) := @solution
#print axioms solution
