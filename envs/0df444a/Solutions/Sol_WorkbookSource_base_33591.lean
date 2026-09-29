-- Prove2me | solution 1 for WorkbookSource.base_33591
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:32.668951+00:00
-- url     : https://prove2.me/submissions/6dfa93dc-7063-4deb-9481-bc25d91246e1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + b + c = 1) :
  3 / 20 ≤ a ^ 2 / 4 + b ^ 2 / 4 + c ^ 2 / 4 + a * b / 5 + b * c / 5 + c * a / 5  := by
  have hw0 : 0 ≤ (a + b + c - 1) := by linarith only [h]
  have hw1 : 0 ≤ (-a - b - c + 1) := by linarith only [h]
  have hsum : 0 ≤ (1/4 : ℝ) * (1) * (2*a/5 + 2*b/5 + c - 3/5)^2 + (21/100 : ℝ) * (1) * (2*a/7 + b - 3/7)^2 + (27/140 : ℝ) * (1) * (a - 1/3)^2 + (3/10 : ℝ) * ((a + b + c - 1)) * (1)^2 := by positivity
  have hid : ( a ^ 2 / 4 + b ^ 2 / 4 + c ^ 2 / 4 + a * b / 5 + b * c / 5 + c * a / 5  ) - (
  3 / 20 ) = (1/4 : ℝ) * (1) * (2*a/5 + 2*b/5 + c - 3/5)^2 + (21/100 : ℝ) * (1) * (2*a/7 + b - 3/7)^2 + (27/140 : ℝ) * (1) * (a - 1/3)^2 + (3/10 : ℝ) * ((a + b + c - 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + b + c = 1), 3 / 20 ≤ a ^ 2 / 4 + b ^ 2 / 4 + c ^ 2 / 4 + a * b / 5 + b * c / 5 + c * a / 5) := @solution
#print axioms solution
