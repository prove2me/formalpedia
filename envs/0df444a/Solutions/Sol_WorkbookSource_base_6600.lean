-- Prove2me | solution 1 for WorkbookSource.base_6600
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:44:24.555678+00:00
-- url     : https://prove2.me/submissions/477ff67d-6fc3-42c0-8abc-4c9e356afe30

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a + b + c) ^ 2 / (a ^ 2 + 11 * b * c) + (2 * b + c + a) ^ 2 / (b ^ 2 + 11 * c * a) + (2 * c + a + b) ^ 2 / (c ^ 2 + 11 * a * b) ≥ 4  := by
  have hn : 0 ≤ (11*a^5*b + 11*a^5*c + 45*a^4*b^2 + 44*a^4*b*c + 45*a^4*c^2 + 46*a^3*b^3 + 664*a^3*b^2*c + 664*a^3*b*c^2 + 46*a^3*c^3 + 45*a^2*b^4 + 664*a^2*b^3*c - 4590*a^2*b^2*c^2 + 664*a^2*b*c^3 + 45*a^2*c^4 + 11*a*b^5 + 44*a*b^4*c + 664*a*b^3*c^2 + 664*a*b^2*c^3 + 44*a*b*c^4 + 11*a*c^5 + 11*b^5*c + 45*b^4*c^2 + 46*b^3*c^3 + 45*b^2*c^4 + 11*b*c^5) := by
    have hs0 : 0 ≤ (45 : ℝ) * (1) * (-a^2*b - 89*a^2*c/180 - 89*a*b^2/180 + 89*a*c^2/180 + 89*b^2*c/180 + b*c^2)^2 := by positivity
    have hs1 : 0 ≤ (24479/720 : ℝ) * (1) * (-a^2*c + 89*a*b^2/91 - 89*a*c^2/91 + b^2*c)^2 := by positivity
    have hs2 : 0 ≤ (269/182 : ℝ) * (1) * (-a*b^2 + a*c^2)^2 := by positivity
    have hs3 : 0 ≤ (1393/2 : ℝ) * (b*c) * (-a*b + a*c + 12*b^2/1393 - 12*c^2/1393)^2 := by positivity
    have hs4 : 0 ≤ (47/2 : ℝ) * (b*c) * (-a^2 + b*c)^2 := by positivity
    have hs5 : 0 ≤ (15251/1393 : ℝ) * (b*c) * (-b^2 + c^2)^2 := by positivity
    have hs6 : 0 ≤ (1393/2 : ℝ) * (a*c) * (12*a^2/1393 - a*b + b*c - 12*c^2/1393)^2 := by positivity
    have hs7 : 0 ≤ (47/2 : ℝ) * (a*c) * (-a*c + b^2)^2 := by positivity
    have hs8 : 0 ≤ (15251/1393 : ℝ) * (a*c) * (-a^2 + c^2)^2 := by positivity
    have hs9 : 0 ≤ (1393/2 : ℝ) * (a*b) * (12*a^2/1393 - a*c - 12*b^2/1393 + b*c)^2 := by positivity
    have hs10 : 0 ≤ (47/2 : ℝ) * (a*b) * (-a*b + c^2)^2 := by positivity
    have hs11 : 0 ≤ (15251/1393 : ℝ) * (a*b) * (-a^2 + b^2)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11]
  field_simp (disch := positivity)
  nlinarith only [hn]

example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (2 * a + b + c) ^ 2 / (a ^ 2 + 11 * b * c) + (2 * b + c + a) ^ 2 / (b ^ 2 + 11 * c * a) + (2 * c + a + b) ^ 2 / (c ^ 2 + 11 * a * b) ≥ 4) := @solution
#print axioms solution
