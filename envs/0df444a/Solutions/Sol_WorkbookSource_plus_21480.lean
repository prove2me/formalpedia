-- Prove2me | solution 1 for WorkbookSource.plus_21480
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:42.254196+00:00
-- url     : https://prove2.me/submissions/9f502931-018a-4a30-94d3-d2fee8860e85

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a^3 + b^3 + c^3 + 3 * a * b * c)^2 ≥ 4 * (a * b + b * c + c * a) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)   := by
  have h0 : 0 ≤ (38/9 : ℝ) * (1) * (a^3/3 - a^2*b/3 - a^2*c/3 - a*b^2/3 + a*b*c - a*c^2/3 + b^3/3 - b^2*c/3 - b*c^2/3 + c^3/3)^2 := by positivity
  have h1 : 0 ≤ (85/81 : ℝ) * (1) * (43*a^3/170 + 89*a^2*b/170 - a^2*c/2 - a*b^2/2 + 19*a*c^2/85 - 47*b^3/170 - 127*b^2*c/170 + b*c^2 + 2*c^3/85)^2 := by positivity
  have h2 : 0 ≤ (2288/2295 : ℝ) * (1) * (-401*a^3/1144 - 743*a^2*b/1144 - 765*a^2*c/1144 + 765*a*b^2/1144 + a*c^2 + 379*b^3/1144 - 401*b^2*c/1144 + c^3/52)^2 := by positivity
  have h3 : 0 ≤ (62/117 : ℝ) * (1) * (-a^3/2 + a^2*b/2 - a^2*c/2 + a*b^2/2 - b^3/2 - b^2*c/2 + c^3)^2 := by positivity
  have h4 : 0 ≤ (62/297 : ℝ) * (1) * (a^3 - a^2*b - a^2*c + a*b^2 - b^3 + b^2*c)^2 := by positivity
  have h5 : 0 ≤ (8/9 : ℝ) * (b*c) * (-a*b/2 + a*c/2 - b^2 + c^2)^2 := by positivity
  have h6 : 0 ≤ (8/9 : ℝ) * (a*c) * (-a^2 - a*b/2 + b*c/2 + c^2)^2 := by positivity
  have h7 : 0 ≤ (8/9 : ℝ) * (a*b) * (-a^2 - a*c/2 + b^2 + b*c/2)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), (a^3 + b^3 + c^3 + 3 * a * b * c)^2 ≥ 4 * (a * b + b * c + c * a) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)) := @solution
#print axioms solution
