-- Prove2me | solution 1 for WorkbookSource.base_50368
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:03:30.35873+00:00
-- url     : https://prove2.me/submissions/cc4ac3e9-0509-4c65-92fe-ea88a0e923c7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a + b + c + 1) * (a + 1) * (b + 1) * (c + 1) ≥ 8 * (a * b + b * c + c * a + a * b * c)  := by
  have h0 : 0 ≤ (1 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 := by positivity
  have h1 : 0 ≤ (8/9 : ℝ) * (1) * (-a/2 - b/2 + c)^2 := by positivity
  have h2 : 0 ≤ (2/3 : ℝ) * (1) * (-a + b)^2 := by positivity
  have h3 : 0 ≤ (8/3 : ℝ) * (c) * (-a/2 - b/2 + 1)^2 := by positivity
  have h4 : 0 ≤ (1/3 : ℝ) * (c) * (-a + b)^2 := by positivity
  have h5 : 0 ≤ (8/3 : ℝ) * (b) * (-a/2 - c/2 + 1)^2 := by positivity
  have h6 : 0 ≤ (1/3 : ℝ) * (b) * (-a + c)^2 := by positivity
  have h7 : 0 ≤ (1 : ℝ) * (b*c) * (1 - a)^2 := by positivity
  have h8 : 0 ≤ (8/3 : ℝ) * (a) * (-b/2 - c/2 + 1)^2 := by positivity
  have h9 : 0 ≤ (1/3 : ℝ) * (a) * (-b + c)^2 := by positivity
  have h10 : 0 ≤ (1 : ℝ) * (a*c) * (1 - b)^2 := by positivity
  have h11 : 0 ≤ (1 : ℝ) * (a*b) * (1 - c)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0), (a + b + c + 1) * (a + 1) * (b + 1) * (c + 1) ≥ 8 * (a * b + b * c + c * a + a * b * c)) := @solution
#print axioms solution
