-- Prove2me | solution 1 for WorkbookSource.base_20423
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:22.179825+00:00
-- url     : https://prove2.me/submissions/fdb053a2-4583-45a2-8fab-2dce1c68cbda

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 4) :
  3 * (a^4 + b^4 + c^4 + d^4 + 12 * a * b * c * d) + 80 ≥ 8 * (a + b + c + d)^2  := by
  have hw0 : 0 ≤ (a^2 + b^2 + c^2 + d^2 - 4) := by linarith only [h]
  have hw1 : 0 ≤ (-a^2 - b^2 - c^2 - d^2 + 4) := by linarith only [h]
  have hsum : 0 ≤ (10 : ℝ) * (1) * (a^2/5 + 3*a*b/5 - 2*a*c/5 - 2*a*d/5 + b^2/5 - 2*b*c/5 - 2*b*d/5 - c^2/5 + c*d - d^2/5)^2 + (42/5 : ℝ) * (1) * (a^2/3 - 4*a*b/21 + 11*a*c/21 - 2*a*d/3 - b^2/7 - 2*b*c/3 + b*d + c^2/7 - d^2/3)^2 + (128/21 : ℝ) * (1) * (-7*a^2/16 - a*b/8 + a*c - 7*a*d/16 + 9*b^2/16 - 7*b*c/16 - 9*c^2/16 + 7*d^2/16)^2 + (6 : ℝ) * (1) * (-a^2/2 + a*b - a*d/2 - b^2/2 - b*c/2 + c^2/2 + d^2/2)^2 + (2 : ℝ) * (1) * (a^2 - a*d - b^2 + b*c - c^2 + d^2)^2 + (20 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (1)^2 + (15/4 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (-a/3 - b/3 - c/3 + d)^2 + (10/3 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (-a/2 - b/2 + c)^2 + (5/2 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (-a + b)^2 + (3/4 : ℝ) * ((a^2 + b^2 + c^2 + d^2 - 4)) * (a + b + c + d)^2 := by positivity
  have hid : (
  3 * (a^4 + b^4 + c^4 + d^4 + 12 * a * b * c * d) + 80 ) - ( 8 * (a + b + c + d)^2  ) = (10 : ℝ) * (1) * (a^2/5 + 3*a*b/5 - 2*a*c/5 - 2*a*d/5 + b^2/5 - 2*b*c/5 - 2*b*d/5 - c^2/5 + c*d - d^2/5)^2 + (42/5 : ℝ) * (1) * (a^2/3 - 4*a*b/21 + 11*a*c/21 - 2*a*d/3 - b^2/7 - 2*b*c/3 + b*d + c^2/7 - d^2/3)^2 + (128/21 : ℝ) * (1) * (-7*a^2/16 - a*b/8 + a*c - 7*a*d/16 + 9*b^2/16 - 7*b*c/16 - 9*c^2/16 + 7*d^2/16)^2 + (6 : ℝ) * (1) * (-a^2/2 + a*b - a*d/2 - b^2/2 - b*c/2 + c^2/2 + d^2/2)^2 + (2 : ℝ) * (1) * (a^2 - a*d - b^2 + b*c - c^2 + d^2)^2 + (20 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (1)^2 + (15/4 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (-a/3 - b/3 - c/3 + d)^2 + (10/3 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (-a/2 - b/2 + c)^2 + (5/2 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (-a + b)^2 + (3/4 : ℝ) * ((a^2 + b^2 + c^2 + d^2 - 4)) * (a + b + c + d)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 4), 3 * (a^4 + b^4 + c^4 + d^4 + 12 * a * b * c * d) + 80 ≥ 8 * (a + b + c + d)^2) := @solution
#print axioms solution
