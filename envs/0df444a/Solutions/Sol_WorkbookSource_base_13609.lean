-- Prove2me | solution 1 for WorkbookSource.base_13609
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:45.331109+00:00
-- url     : https://prove2.me/submissions/a4acfce7-8faf-4c99-bf47-cfa236fb67e1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d e f : ℝ) (h : a + b + c + d + e + f = 0) :
  2 * (a * b + b * c + c * d + d * e + e * f + f * a) ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2  := by
  have hw0 : 0 ≤ (a + b + c + d + e + f) := by linarith only [h]
  have hw1 : 0 ≤ (-a - b - c - d - e - f) := by linarith only [h]
  have hsum : 0 ≤ (7/6 : ℝ) * (1) * (-5*a/7 + b/7 + c/7 + d/7 - 5*e/7 + f)^2 + (8/7 : ℝ) * (1) * (a/4 + b/8 - 3*c/4 + d - 5*e/8)^2 + (9/8 : ℝ) * (1) * (-2*a/3 + b - 2*c/3 + e/3)^2 + (1/6 : ℝ) * ((a + b + c + d + e + f) * (-a - b - c - d - e - f)) * (1)^2 := by positivity
  have hid : ( a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2  ) - (
  2 * (a * b + b * c + c * d + d * e + e * f + f * a) ) = (7/6 : ℝ) * (1) * (-5*a/7 + b/7 + c/7 + d/7 - 5*e/7 + f)^2 + (8/7 : ℝ) * (1) * (a/4 + b/8 - 3*c/4 + d - 5*e/8)^2 + (9/8 : ℝ) * (1) * (-2*a/3 + b - 2*c/3 + e/3)^2 + (1/6 : ℝ) * ((a + b + c + d + e + f) * (-a - b - c - d - e - f)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d e f : ℝ) (h : a + b + c + d + e + f = 0), 2 * (a * b + b * c + c * d + d * e + e * f + f * a) ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2) := @solution
#print axioms solution
