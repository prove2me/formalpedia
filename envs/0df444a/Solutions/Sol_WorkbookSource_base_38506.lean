-- Prove2me | solution 1 for WorkbookSource.base_38506
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:55:48.59251+00:00
-- url     : https://prove2.me/submissions/17d99e33-e3c0-4913-b875-9e683808f422

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^3 + b^3 + c^3 + a * b * c + 1 ≥ a + b + c  := by
  have h0 : 0 ≤ (1 : ℝ) * (1) * (-2*a/3 - 2*b/3 - 2*c/3 + 1)^2 := by positivity
  have h1 : 0 ≤ (7/18 : ℝ) * (1) * (-a/2 - b/2 + c)^2 := by positivity
  have h2 : 0 ≤ (7/24 : ℝ) * (1) * (-a + b)^2 := by positivity
  have h3 : 0 ≤ (1 : ℝ) * (c) * (-a/12 - b/12 + c - 5/12)^2 := by positivity
  have h4 : 0 ≤ (23/144 : ℝ) * (c) * (-a - b + 1)^2 := by positivity
  have h5 : 0 ≤ (1 : ℝ) * (b) * (-a/12 + b - c/12 - 5/12)^2 := by positivity
  have h6 : 0 ≤ (23/144 : ℝ) * (b) * (-a - c + 1)^2 := by positivity
  have h7 : 0 ≤ (1 : ℝ) * (a) * (a - b/12 - c/12 - 5/12)^2 := by positivity
  have h8 : 0 ≤ (23/144 : ℝ) * (a) * (-b - c + 1)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0), a^3 + b^3 + c^3 + a * b * c + 1 ≥ a + b + c) := @solution
#print axioms solution
