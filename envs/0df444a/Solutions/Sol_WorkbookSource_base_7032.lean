-- Prove2me | solution 1 for WorkbookSource.base_7032
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:41:01.214125+00:00
-- url     : https://prove2.me/submissions/dfe582f5-3ead-40f4-877b-295f990366d9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a^2 + b^2 + c^2 = 6) : (a - b)^4 + (b - c)^4 + (c - a)^4 ≤ 162  := by
  have hw0 : 0 ≤ (a^2 + b^2 + c^2 - 6) := by linarith only [h]
  have hw1 : 0 ≤ (-a^2 - b^2 - c^2 + 6) := by linarith only [h]
  have hsum : 0 ≤ (4 : ℝ) * (1) * (-7*a^2/24 + a*b/4 + a*c/4 + 11*b^2/24 + b*c + 11*c^2/24 + 1/4)^2 + (15/4 : ℝ) * (1) * (17*a^2/30 + a*b/5 + a*c - 13*b^2/30 + 11*c^2/30 + 1/5)^2 + (18/5 : ℝ) * (1) * (17*a^2/36 + a*b + 17*b^2/36 - 19*c^2/36 + 1/6)^2 + (323/12 : ℝ) * ((-a^2 - b^2 - c^2 + 6)) * (1)^2 + (313/72 : ℝ) * ((-a^2 - b^2 - c^2 + 6)) * (-12*a/313 - 12*b/313 + c)^2 + (97825/22536 : ℝ) * ((-a^2 - b^2 - c^2 + 6)) * (-12*a/301 + b)^2 + (93925/21672 : ℝ) * ((-a^2 - b^2 - c^2 + 6)) * (a)^2 := by positivity
  have hid : ( 162  ) - ( (a - b)^4 + (b - c)^4 + (c - a)^4 ) = (4 : ℝ) * (1) * (-7*a^2/24 + a*b/4 + a*c/4 + 11*b^2/24 + b*c + 11*c^2/24 + 1/4)^2 + (15/4 : ℝ) * (1) * (17*a^2/30 + a*b/5 + a*c - 13*b^2/30 + 11*c^2/30 + 1/5)^2 + (18/5 : ℝ) * (1) * (17*a^2/36 + a*b + 17*b^2/36 - 19*c^2/36 + 1/6)^2 + (323/12 : ℝ) * ((-a^2 - b^2 - c^2 + 6)) * (1)^2 + (313/72 : ℝ) * ((-a^2 - b^2 - c^2 + 6)) * (-12*a/313 - 12*b/313 + c)^2 + (97825/22536 : ℝ) * ((-a^2 - b^2 - c^2 + 6)) * (-12*a/301 + b)^2 + (93925/21672 : ℝ) * ((-a^2 - b^2 - c^2 + 6)) * (a)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a^2 + b^2 + c^2 = 6), (a - b)^4 + (b - c)^4 + (c - a)^4 ≤ 162) := @solution
#print axioms solution
