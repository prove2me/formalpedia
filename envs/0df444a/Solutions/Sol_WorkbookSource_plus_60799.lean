-- Prove2me | solution 1 for WorkbookSource.plus_60799
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:48.403216+00:00
-- url     : https://prove2.me/submissions/870292e7-6f85-4a87-9f64-8470ff397054

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 27 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ 8 * (a * b + b * c + c * a)^3   := by
  have h0 : 0 ≤ (27 : ℝ) * (1) * (a^2*b/27 - 4*a^2*c/9 - 4*a*b^2/9 - 4*b^2*c/27 + b*c^2)^2 := by positivity
  have h1 : 0 ≤ (27 : ℝ) * (1) * (-4*a^2*b/9 - 4*a^2*c/27 + a*b^2/27 + a*c^2 - 4*b^2*c/9)^2 := by positivity
  have h2 : 0 ≤ (584/27 : ℝ) * (1) * (-21*a^2*b/146 - 58*a^2*c/73 + a*b^2 - 9*b^2*c/146)^2 := by positivity
  have h3 : 0 ≤ (41750/1971 : ℝ) * (1) * (a^2*b - 30*a^2*c/167 - 137*b^2*c/167)^2 := by positivity
  have h4 : 0 ≤ (1125/167 : ℝ) * (1) * (-a^2*c + b^2*c)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), 27 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ 8 * (a * b + b * c + c * a)^3) := @solution
#print axioms solution
