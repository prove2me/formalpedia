-- Prove2me | solution 1 for WorkbookSource.plus_68598
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:50.263329+00:00
-- url     : https://prove2.me/submissions/91c87f48-657d-4314-bcac-f333a219d43b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 * b + a^4 * c + b^4 * c + b * c^4 ≥ a * b^2 * c^2   := by
  have h0 : 0 ≤ (1 : ℝ) * (c) * (-a^2/7 + b^2 - b*c/8)^2 := by positivity
  have h1 : 0 ≤ (48/49 : ℝ) * (c) * (a^2 - 7*b*c/384)^2 := by positivity
  have h2 : 0 ≤ (2/7 : ℝ) * (c) * (a*b - 7*b*c/8)^2 := by positivity
  have h3 : 0 ≤ (47/3072 : ℝ) * (c) * (b*c)^2 := by positivity
  have h4 : 0 ≤ (1 : ℝ) * (b) * (-a^2/7 - b*c/8 + c^2)^2 := by positivity
  have h5 : 0 ≤ (48/49 : ℝ) * (b) * (a^2 - 7*b*c/384)^2 := by positivity
  have h6 : 0 ≤ (2/7 : ℝ) * (b) * (a*c - 7*b*c/8)^2 := by positivity
  have h7 : 0 ≤ (47/3072 : ℝ) * (b) * (b*c)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^4 * b + a^4 * c + b^4 * c + b * c^4 ≥ a * b^2 * c^2) := @solution
#print axioms solution
