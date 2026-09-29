-- Prove2me | solution 1 for WorkbookSource.plus_12600
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:37.23377+00:00
-- url     : https://prove2.me/submissions/ac274882-2675-488e-85fa-5f77efc8a67b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (h1 : a * b + b * c + c * d = 7) (h2 : a * c + b * d = 3) : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ 73 / 8   := by
  have hw0 : 0 ≤ (a*b + b*c + c*d - 7) := by linarith only [h1]
  have hw1 : 0 ≤ (-a*b - b*c - c*d + 7) := by linarith only [h1]
  have hw2 : 0 ≤ (a*c + b*d - 3) := by linarith only [h2]
  have hw3 : 0 ≤ (-a*c - b*d + 3) := by linarith only [h2]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (31*b/64 - 55*c/64 + d)^2 + (1 : ℝ) * (1) * (a - 55*b/64 + 31*c/64)^2 + (55/2048 : ℝ) * (1) * (-b + c)^2 + (31/32 : ℝ) * ((-a*c - b*d + 3)) * (1)^2 + (55/32 : ℝ) * ((a*b + b*c + c*d - 7)) * (1)^2 := by positivity
  have hid : ( a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ) - ( 73 / 8   ) = (1 : ℝ) * (1) * (31*b/64 - 55*c/64 + d)^2 + (1 : ℝ) * (1) * (a - 55*b/64 + 31*c/64)^2 + (55/2048 : ℝ) * (1) * (-b + c)^2 + (31/32 : ℝ) * ((-a*c - b*d + 3)) * (1)^2 + (55/32 : ℝ) * ((a*b + b*c + c*d - 7)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (h1 : a * b + b * c + c * d = 7) (h2 : a * c + b * d = 3), a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ 73 / 8) := @solution
#print axioms solution
