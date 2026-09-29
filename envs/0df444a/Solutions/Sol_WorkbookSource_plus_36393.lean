-- Prove2me | solution 1 for WorkbookSource.plus_36393
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:40.268195+00:00
-- url     : https://prove2.me/submissions/4e7aa5b4-d337-44dc-ba00-bdbf64da3833

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (hab : a * b + b * c = 12) (hac : a * c + b * d = 3) : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ 154 / 9   := by
  have hw0 : 0 ≤ (a*b + b*c - 12) := by linarith only [hab]
  have hw1 : 0 ≤ (-a*b - b*c + 12) := by linarith only [hab]
  have hw2 : 0 ≤ (a*c + b*d - 3) := by linarith only [hac]
  have hw3 : 0 ≤ (-a*c - b*d + 3) := by linarith only [hac]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (b/9 + d)^2 + (1 : ℝ) * (1) * (a/9 - 20*b/27 + c)^2 + (80/81 : ℝ) * (1) * (a - 2*b/3)^2 + (2/9 : ℝ) * ((-a*c - b*d + 3)) * (1)^2 + (40/27 : ℝ) * ((a*b + b*c - 12)) * (1)^2 := by positivity
  have hid : ( a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ) - ( 154 / 9   ) = (1 : ℝ) * (1) * (b/9 + d)^2 + (1 : ℝ) * (1) * (a/9 - 20*b/27 + c)^2 + (80/81 : ℝ) * (1) * (a - 2*b/3)^2 + (2/9 : ℝ) * ((-a*c - b*d + 3)) * (1)^2 + (40/27 : ℝ) * ((a*b + b*c - 12)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (hab : a * b + b * c = 12) (hac : a * c + b * d = 3), a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ 154 / 9) := @solution
#print axioms solution
