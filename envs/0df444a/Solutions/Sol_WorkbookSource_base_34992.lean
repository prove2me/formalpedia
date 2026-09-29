-- Prove2me | solution 1 for WorkbookSource.base_34992
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:33.434711+00:00
-- url     : https://prove2.me/submissions/c3f6e35a-5fce-4303-9e45-cfb62658c705

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 4) :
  a^4 + b^4 + c^4 + d^4 + (4 / 3) * (a + b + c + d)^2 ≤ (76 / 3)  := by
  have hw0 : 0 ≤ (a^2 + b^2 + c^2 + d^2 - 4) := by linarith only [h]
  have hw1 : 0 ≤ (-a^2 - b^2 - c^2 - d^2 + 4) := by linarith only [h]
  have hsum : 0 ≤ (8/3 : ℝ) * (1) * (a^2/8 - a*c/4 - a*d/4 + b^2/8 - b*c/4 - b*d/4 - c^2/8 + c*d - d^2/8)^2 + (8/3 : ℝ) * (1) * (-a^2/8 + a*b - a*c/4 - a*d/4 - b^2/8 - b*c/4 - b*d/4 + c^2/8 + d^2/8)^2 + (7/3 : ℝ) * (1) * (a^2/7 - a*c/7 - 3*a*d/7 - b^2/7 - 3*b*c/7 + b*d + c^2/7 - d^2/7)^2 + (16/7 : ℝ) * (1) * (-a^2/8 + a*c - a*d/2 + b^2/8 - b*c/2 - c^2/8 + d^2/8)^2 + (4/3 : ℝ) * (1) * (a^2/4 - a*d - b^2/4 + b*c - c^2/4 + d^2/4)^2 + (19/3 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (1)^2 + (5/4 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (-4*a/15 - 4*b/15 - 4*c/15 + d)^2 + (209/180 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (-4*a/11 - 4*b/11 + c)^2 + (133/132 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (-4*a/7 + b)^2 + (19/28 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (a)^2 := by positivity
  have hid : ( (76 / 3)  ) - (
  a^4 + b^4 + c^4 + d^4 + (4 / 3) * (a + b + c + d)^2 ) = (8/3 : ℝ) * (1) * (a^2/8 - a*c/4 - a*d/4 + b^2/8 - b*c/4 - b*d/4 - c^2/8 + c*d - d^2/8)^2 + (8/3 : ℝ) * (1) * (-a^2/8 + a*b - a*c/4 - a*d/4 - b^2/8 - b*c/4 - b*d/4 + c^2/8 + d^2/8)^2 + (7/3 : ℝ) * (1) * (a^2/7 - a*c/7 - 3*a*d/7 - b^2/7 - 3*b*c/7 + b*d + c^2/7 - d^2/7)^2 + (16/7 : ℝ) * (1) * (-a^2/8 + a*c - a*d/2 + b^2/8 - b*c/2 - c^2/8 + d^2/8)^2 + (4/3 : ℝ) * (1) * (a^2/4 - a*d - b^2/4 + b*c - c^2/4 + d^2/4)^2 + (19/3 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (1)^2 + (5/4 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (-4*a/15 - 4*b/15 - 4*c/15 + d)^2 + (209/180 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (-4*a/11 - 4*b/11 + c)^2 + (133/132 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (-4*a/7 + b)^2 + (19/28 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 4)) * (a)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 4), a^4 + b^4 + c^4 + d^4 + (4 / 3) * (a + b + c + d)^2 ≤ (76 / 3)) := @solution
#print axioms solution
