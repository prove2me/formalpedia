-- Prove2me | solution 1 for WorkbookSource.plus_28964
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:44.399468+00:00
-- url     : https://prove2.me/submissions/9034a58b-5f20-4dc9-9355-dac62348fbd2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a + b) * (b + c) * (c + a) * (1 + a) * (1 + b) * (1 + c) ≥ a * b * c * (2 + a + b) * (2 + b + c) * (2 + c + a)   := by
  have h0 : 0 ≤ (1 : ℝ) * (c) * (-a*c - a + b*c + b)^2 := by positivity
  have h1 : 0 ≤ (1 : ℝ) * (b) * (-a*b - a + b*c + c)^2 := by positivity
  have h2 : 0 ≤ (1 : ℝ) * (b*c) * (-b + c)^2 := by positivity
  have h3 : 0 ≤ (1 : ℝ) * (a) * (-a*b + a*c - b + c)^2 := by positivity
  have h4 : 0 ≤ (1 : ℝ) * (a*c) * (-a + c)^2 := by positivity
  have h5 : 0 ≤ (1 : ℝ) * (a*b) * (-a + b)^2 := by positivity
  have h6 : 0 ≤ (2 : ℝ) * (a*b*c) * (-a/2 - b/2 + c)^2 := by positivity
  have h7 : 0 ≤ (3/2 : ℝ) * (a*b*c) * (-a + b)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0), (a + b) * (b + c) * (c + a) * (1 + a) * (1 + b) * (1 + c) ≥ a * b * c * (2 + a + b) * (2 + b + c) * (2 + c + a)) := @solution
#print axioms solution
