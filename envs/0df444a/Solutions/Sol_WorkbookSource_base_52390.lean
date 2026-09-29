-- Prove2me | solution 1 for WorkbookSource.base_52390
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:28:54.955184+00:00
-- url     : https://prove2.me/submissions/dfbc2a17-efc1-408f-bf1c-ccfa5571bc97

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (a b c d e : ℝ) :
  5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) ≤
    (a + b + c + d + e) ^ 2 + 2 * ((3 * a - b - c - d) ^ 2 + (3 * b - c - d - e) ^ 2 + (3 * c - d - e - a) ^ 2 + (3 * d - e - a - b) ^ 2 + (3 * e - a - b - c) ^ 2)  := by
  have hsum : 0 ≤ (20 : ℝ) * (-a/20 - 9*b/20 - 9*c/20 - d/20 + e)^2 + (399/20 : ℝ) * (-181*a/399 - 9*b/19 - 29*c/399 + d)^2 + (6322/399 : ℝ) * (-37*a/58 - 21*b/58 + c)^2 + (545/58 : ℝ) * (-a + b)^2 := by positivity
  have hid : (
    (a + b + c + d + e) ^ 2 + 2 * ((3 * a - b - c - d) ^ 2 + (3 * b - c - d - e) ^ 2 + (3 * c - d - e - a) ^ 2 + (3 * d - e - a - b) ^ 2 + (3 * e - a - b - c) ^ 2)  ) - (
  5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) ) = (20 : ℝ) * (-a/20 - 9*b/20 - 9*c/20 - d/20 + e)^2 + (399/20 : ℝ) * (-181*a/399 - 9*b/19 - 29*c/399 + d)^2 + (6322/399 : ℝ) * (-37*a/58 - 21*b/58 + c)^2 + (545/58 : ℝ) * (-a + b)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d e : ℝ), 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) ≤
    (a + b + c + d + e) ^ 2 + 2 * ((3 * a - b - c - d) ^ 2 + (3 * b - c - d - e) ^ 2 + (3 * c - d - e - a) ^ 2 + (3 * d - e - a - b) ^ 2 + (3 * e - a - b - c) ^ 2)) := @solution
#print axioms solution
