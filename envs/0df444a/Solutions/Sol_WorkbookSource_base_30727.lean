-- Prove2me | solution 1 for WorkbookSource.base_30727
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:55:46.1586+00:00
-- url     : https://prove2.me/submissions/6f8c73d2-faaa-498b-91f3-3230c28997a2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) * (b + c) * (c + a) * (a + b - c) * (b + c - a) * (c + a - b) ≤ 8 * a ^ 2 * b ^ 2 * c ^ 2  := by
  have h0 : 0 ≤ (1 : ℝ) * (1) * (a^2*b/2 - a^2*c/2 - a*b^2/2 + a*c^2/2 - b^2*c + b*c^2)^2 := by positivity
  have h1 : 0 ≤ (3/4 : ℝ) * (1) * (-a^2*b - a^2*c + a*b^2 + a*c^2)^2 := by positivity
  have h2 : 0 ≤ (1 : ℝ) * (b*c) * (-a^2/2 + a*b - a*c/2 - b^2/2 - b*c/2 + c^2)^2 := by positivity
  have h3 : 0 ≤ (3/4 : ℝ) * (b*c) * (a^2 - a*c - b^2 + b*c)^2 := by positivity
  have h4 : 0 ≤ (1 : ℝ) * (a*c) * (-a^2/2 + a*b - a*c/2 - b^2/2 - b*c/2 + c^2)^2 := by positivity
  have h5 : 0 ≤ (3/4 : ℝ) * (a*c) * (a^2 - a*c - b^2 + b*c)^2 := by positivity
  have h6 : 0 ≤ (1 : ℝ) * (a*b) * (-a^2/2 + a*b - a*c/2 - b^2/2 - b*c/2 + c^2)^2 := by positivity
  have h7 : 0 ≤ (3/4 : ℝ) * (a*b) * (a^2 - a*c - b^2 + b*c)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) * (b + c) * (c + a) * (a + b - c) * (b + c - a) * (c + a - b) ≤ 8 * a ^ 2 * b ^ 2 * c ^ 2) := @solution
#print axioms solution
