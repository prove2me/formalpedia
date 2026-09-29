-- Prove2me | solution 1 for WorkbookSource.base_26207
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:23.553794+00:00
-- url     : https://prove2.me/submissions/f8357dde-c854-43b3-901e-d14245167266

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (h : a * d - 3 * b * c = 1) :
  a^2 + b^2 + 3 * c^2 + d^2 + a * c + b * d ≥ 1  := by
  have hw0 : 0 ≤ (a*d - 3*b*c - 1) := by linarith only [h]
  have hw1 : 0 ≤ (-a*d + 3*b*c + 1) := by linarith only [h]
  have hsum : 0 ≤ (3 : ℝ) * (1) * (a/6 + b/2 + c)^2 + (1 : ℝ) * (1) * (-a/2 + b/2 + d)^2 + (2/3 : ℝ) * (1) * (a)^2 + (1 : ℝ) * ((a*d - 3*b*c - 1)) * (1)^2 := by positivity
  have hid : (
  a^2 + b^2 + 3 * c^2 + d^2 + a * c + b * d ) - ( 1  ) = (3 : ℝ) * (1) * (a/6 + b/2 + c)^2 + (1 : ℝ) * (1) * (-a/2 + b/2 + d)^2 + (2/3 : ℝ) * (1) * (a)^2 + (1 : ℝ) * ((a*d - 3*b*c - 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (h : a * d - 3 * b * c = 1), a^2 + b^2 + 3 * c^2 + d^2 + a * c + b * d ≥ 1) := @solution
#print axioms solution
