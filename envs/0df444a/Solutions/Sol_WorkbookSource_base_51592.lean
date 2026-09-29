-- Prove2me | solution 1 for WorkbookSource.base_51592
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:25.973036+00:00
-- url     : https://prove2.me/submissions/abc32188-631a-45ed-9c70-138529193dc8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (hab : a * b + b * c + c * d + d * a = 1) :
  a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2 + 4 * d ^ 2 ≥ 2  := by
  have hw0 : 0 ≤ (a*b + a*d + b*c + c*d - 1) := by linarith only [hab]
  have hw1 : 0 ≤ (-a*b - a*d - b*c - c*d + 1) := by linarith only [hab]
  have hsum : 0 ≤ (4 : ℝ) * (1) * (-a/4 - c/4 + d)^2 + (11/4 : ℝ) * (1) * (-a/11 - 4*b/11 + c)^2 + (18/11 : ℝ) * (1) * (-2*a/3 + b)^2 + (2 : ℝ) * ((a*b + a*d + b*c + c*d - 1)) * (1)^2 := by positivity
  have hid : (
  a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2 + 4 * d ^ 2 ) - ( 2  ) = (4 : ℝ) * (1) * (-a/4 - c/4 + d)^2 + (11/4 : ℝ) * (1) * (-a/11 - 4*b/11 + c)^2 + (18/11 : ℝ) * (1) * (-2*a/3 + b)^2 + (2 : ℝ) * ((a*b + a*d + b*c + c*d - 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (hab : a * b + b * c + c * d + d * a = 1), a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2 + 4 * d ^ 2 ≥ 2) := @solution
#print axioms solution
