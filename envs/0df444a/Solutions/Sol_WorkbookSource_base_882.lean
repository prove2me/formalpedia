-- Prove2me | solution 1 for WorkbookSource.base_882
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:04:08.331852+00:00
-- url     : https://prove2.me/submissions/2bddb465-aca8-44eb-b52b-4718a8cee0ff

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + b + c) ^ 4 ≥ 16 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)  := by
  have h0 : 0 ≤ (1 : ℝ) * (1) * (-a^2/2 + a*b - a*c/2 - b^2/2 - b*c/2 + c^2)^2 := by positivity
  have h1 : 0 ≤ (3/4 : ℝ) * (1) * (a^2 - a*c - b^2 + b*c)^2 := by positivity
  have h2 : 0 ≤ (9 : ℝ) * (b*c) * (a + b/9 - c/9)^2 := by positivity
  have h3 : 0 ≤ (44/9 : ℝ) * (b*c) * (-b + c)^2 := by positivity
  have h4 : 0 ≤ (9 : ℝ) * (a*c) * (a/9 + b - c/9)^2 := by positivity
  have h5 : 0 ≤ (44/9 : ℝ) * (a*c) * (-a + c)^2 := by positivity
  have h6 : 0 ≤ (15 : ℝ) * (a*b) * (c)^2 := by positivity
  have h7 : 0 ≤ (5 : ℝ) * (a*b) * (-a + b)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), (a + b + c) ^ 4 ≥ 16 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)) := @solution
#print axioms solution
