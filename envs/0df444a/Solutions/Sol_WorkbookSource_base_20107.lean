-- Prove2me | solution 1 for WorkbookSource.base_20107
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:31:48.575636+00:00
-- url     : https://prove2.me/submissions/eaca7919-28cb-4449-9b08-542de718eb85

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 3 * (a^2 + b^2 + c^2 + d^2 + e^2) + (a * b + b * c + c * d + d * e + e * a) ≥ 4 * (a * c + b * d + c * e + d * a + e * b)  := by
  have hsum : 0 ≤ (3 : ℝ) * (1) * (a/6 - 2*b/3 - 2*c/3 + d/6 + e)^2 + (35/12 : ℝ) * (1) * (-5*a/7 - 4*b/7 + 2*c/7 + d)^2 + (10/7 : ℝ) * (1) * (-3*a/4 - b/4 + c)^2 + (5/8 : ℝ) * (1) * (-a + b)^2 := by positivity
  have hid : ( 3 * (a^2 + b^2 + c^2 + d^2 + e^2) + (a * b + b * c + c * d + d * e + e * a) ) - ( 4 * (a * c + b * d + c * e + d * a + e * b)  ) = (3 : ℝ) * (1) * (a/6 - 2*b/3 - 2*c/3 + d/6 + e)^2 + (35/12 : ℝ) * (1) * (-5*a/7 - 4*b/7 + 2*c/7 + d)^2 + (10/7 : ℝ) * (1) * (-3*a/4 - b/4 + c)^2 + (5/8 : ℝ) * (1) * (-a + b)^2 := by ring
  linarith only [hsum, hid]
example : (∀ {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e), 3 * (a^2 + b^2 + c^2 + d^2 + e^2) + (a * b + b * c + c * d + d * e + e * a) ≥ 4 * (a * c + b * d + c * e + d * a + e * b)) := @solution
#print axioms solution
