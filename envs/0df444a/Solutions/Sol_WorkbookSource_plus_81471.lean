-- Prove2me | solution 1 for WorkbookSource.plus_81471
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:46.106318+00:00
-- url     : https://prove2.me/submissions/fca677c7-4409-4e23-932b-d02f76aaf581

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d x y : ℝ) (h1 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≤ 1 / 16) (h2 : x ^ 2 + y ^ 2 = 1) : (a * x + b * y) ^ 2 + (c * x + d * y) ^ 2 ≤ 1 / 16   := by
  have hw0 : 0 ≤ (-a^2 - b^2 - c^2 - d^2 + 1/16) := by linarith only [h1]
  have hw1 : 0 ≤ (x^2 + y^2 - 1) := by linarith only [h2]
  have hw2 : 0 ≤ (-x^2 - y^2 + 1) := by linarith only [h2]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (-c*y + d*x)^2 + (1 : ℝ) * (1) * (-a*y + b*x)^2 + (1/16 : ℝ) * ((-x^2 - y^2 + 1)) * (1)^2 + (15/29 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1/16)) * (y)^2 + (15/29 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1/16)) * (x)^2 + (14/29 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1/16)) * (1)^2 + (14/29 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1/16) * (x^2 + y^2 - 1)) * (1)^2 := by positivity
  have hid : ( 1 / 16   ) - ( (a * x + b * y) ^ 2 + (c * x + d * y) ^ 2 ) = (1 : ℝ) * (1) * (-c*y + d*x)^2 + (1 : ℝ) * (1) * (-a*y + b*x)^2 + (1/16 : ℝ) * ((-x^2 - y^2 + 1)) * (1)^2 + (15/29 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1/16)) * (y)^2 + (15/29 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1/16)) * (x)^2 + (14/29 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1/16)) * (1)^2 + (14/29 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1/16) * (x^2 + y^2 - 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d x y : ℝ) (h1 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≤ 1 / 16) (h2 : x ^ 2 + y ^ 2 = 1), (a * x + b * y) ^ 2 + (c * x + d * y) ^ 2 ≤ 1 / 16) := @solution
#print axioms solution
