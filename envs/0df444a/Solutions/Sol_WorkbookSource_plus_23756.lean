-- Prove2me | solution 1 for WorkbookSource.plus_23756
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:33:21.30738+00:00
-- url     : https://prove2.me/submissions/940c83b8-702a-4b4c-9cde-2c074a067613

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : (a * b + b * c + c * d + d * a + a * c + b * d) * (a * c * d + b * c * d + b * a * c + a * b * d) ≥ 6 * (a + b + c + d) * a * b * c * d   := by
  have hsum : 0 ≤ (1 : ℝ) * (d) * (-a*b/2 - a*c/2 + b*c)^2 + (3/4 : ℝ) * (d) * (-a*b + a*c)^2 + (1 : ℝ) * (c) * (-a*b/2 - a*d/2 + b*d)^2 + (3/4 : ℝ) * (c) * (-a*b + a*d)^2 + (1 : ℝ) * (b) * (-a*c/2 - a*d/2 + c*d)^2 + (3/4 : ℝ) * (b) * (-a*c + a*d)^2 + (1 : ℝ) * (a) * (-b*c/2 - b*d/2 + c*d)^2 + (3/4 : ℝ) * (a) * (-b*c + b*d)^2 := by positivity
  have hid : ( (a * b + b * c + c * d + d * a + a * c + b * d) * (a * c * d + b * c * d + b * a * c + a * b * d) ) - ( 6 * (a + b + c + d) * a * b * c * d   ) = (1 : ℝ) * (d) * (-a*b/2 - a*c/2 + b*c)^2 + (3/4 : ℝ) * (d) * (-a*b + a*c)^2 + (1 : ℝ) * (c) * (-a*b/2 - a*d/2 + b*d)^2 + (3/4 : ℝ) * (c) * (-a*b + a*d)^2 + (1 : ℝ) * (b) * (-a*c/2 - a*d/2 + c*d)^2 + (3/4 : ℝ) * (b) * (-a*c + a*d)^2 + (1 : ℝ) * (a) * (-b*c/2 - b*d/2 + c*d)^2 + (3/4 : ℝ) * (a) * (-b*c + b*d)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d), (a * b + b * c + c * d + d * a + a * c + b * d) * (a * c * d + b * c * d + b * a * c + a * b * d) ≥ 6 * (a + b + c + d) * a * b * c * d) := @solution
#print axioms solution
