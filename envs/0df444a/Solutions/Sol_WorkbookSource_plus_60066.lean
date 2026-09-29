-- Prove2me | solution 1 for WorkbookSource.plus_60066
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:28.974544+00:00
-- url     : https://prove2.me/submissions/be262950-a48a-46bd-8899-7ead72b23373

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b > 0) (h : a^3 + b^3 = 1 + a * b) : a^4 + b^4 ≥ a + b   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (a*b) := by linarith only [hab]
  have hw3 : 0 ≤ (a^3 - a*b + b^3 - 1) := by linarith only [h]
  have hw4 : 0 ≤ (-a^3 + a*b - b^3 + 1) := by linarith only [h]
  have hsum : 0 ≤ (1/2 : ℝ) * (1) * (-a^2/2 + a*b - a/2 - b^2/2 - b/2 + 1)^2 + (3/8 : ℝ) * (1) * (a^2 - a - b^2 + b)^2 + (1/2 : ℝ) * ((a^3 - a*b + b^3 - 1)) * (1)^2 + (1/2 : ℝ) * ((b) * (a^3 - a*b + b^3 - 1)) * (1)^2 + (1/2 : ℝ) * ((a) * (a^3 - a*b + b^3 - 1)) * (1)^2 := by positivity
  have hid : ( a^4 + b^4 ) - ( a + b   ) = (1/2 : ℝ) * (1) * (-a^2/2 + a*b - a/2 - b^2/2 - b/2 + 1)^2 + (3/8 : ℝ) * (1) * (a^2 - a - b^2 + b)^2 + (1/2 : ℝ) * ((a^3 - a*b + b^3 - 1)) * (1)^2 + (1/2 : ℝ) * ((b) * (a^3 - a*b + b^3 - 1)) * (1)^2 + (1/2 : ℝ) * ((a) * (a^3 - a*b + b^3 - 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b > 0) (h : a^3 + b^3 = 1 + a * b), a^4 + b^4 ≥ a + b) := @solution
#print axioms solution
