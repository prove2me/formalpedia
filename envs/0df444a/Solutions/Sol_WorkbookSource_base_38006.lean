-- Prove2me | solution 1 for WorkbookSource.base_38006
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:13:47.87259+00:00
-- url     : https://prove2.me/submissions/776f9e0c-2ef5-4536-9de7-c4538b2df7bc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (h : a^4 + b^4 + a^2 * b^2 = 60) :
  4 * a^2 + 4 * b^2 - a * b ≥ 30  := by
  have hw0 : 0 ≤ (a^4 + a^2*b^2 + b^4 - 60) := by linarith only [h]
  have hw1 : 0 ≤ (-a^4 - a^2*b^2 - b^4 + 60) := by linarith only [h]
  have hsum : 0 ≤ (3/2 : ℝ) * (1) * (-a^3/12 - a^2*b/12 + a*b^2/12 + a/2 - b^3/6 + b)^2 + (9/8 : ℝ) * (1) * (-a^3/6 + a^2*b/6 - a*b^2/6 + a)^2 + (1/24 : ℝ) * ((-a^4 - a^2*b^2 - b^4 + 60)) * (-a/2 + b)^2 + (1/32 : ℝ) * ((-a^4 - a^2*b^2 - b^4 + 60)) * (a)^2 + (1/2 : ℝ) * ((a^4 + a^2*b^2 + b^4 - 60)) * (1)^2 := by positivity
  have hid : (
  4 * a^2 + 4 * b^2 - a * b ) - ( 30  ) = (3/2 : ℝ) * (1) * (-a^3/12 - a^2*b/12 + a*b^2/12 + a/2 - b^3/6 + b)^2 + (9/8 : ℝ) * (1) * (-a^3/6 + a^2*b/6 - a*b^2/6 + a)^2 + (1/24 : ℝ) * ((-a^4 - a^2*b^2 - b^4 + 60)) * (-a/2 + b)^2 + (1/32 : ℝ) * ((-a^4 - a^2*b^2 - b^4 + 60)) * (a)^2 + (1/2 : ℝ) * ((a^4 + a^2*b^2 + b^4 - 60)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (h : a^4 + b^4 + a^2 * b^2 = 60), 4 * a^2 + 4 * b^2 - a * b ≥ 30) := @solution
#print axioms solution
