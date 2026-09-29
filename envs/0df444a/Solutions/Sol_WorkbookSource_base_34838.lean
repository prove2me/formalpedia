-- Prove2me | solution 1 for WorkbookSource.base_34838
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:32:07.282525+00:00
-- url     : https://prove2.me/submissions/1c52c376-6a1c-4d88-b98f-e5e43e9802f8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2)^4 - a^8 - b^8 - c^8 ≥ 14 * b^2 * c^2 * (b^2 * c^2 + 4 * a^4)  := by
  have hsum : 0 ≤ (14 : ℝ) * (1) * (-a^2*b^2 + a^2*c^2)^2 + (4 : ℝ) * (1) * (-b^3*c + b*c^3)^2 + (4 : ℝ) * (1) * (-a^3*c + a*b^2*c + a*c^3)^2 + (4 : ℝ) * (1) * (-a^3*b + a*b^3 + a*b*c^2)^2 := by positivity
  have hid : ( (a^2 + b^2 + c^2)^4 - a^8 - b^8 - c^8 ) - ( 14 * b^2 * c^2 * (b^2 * c^2 + 4 * a^4)  ) = (14 : ℝ) * (1) * (-a^2*b^2 + a^2*c^2)^2 + (4 : ℝ) * (1) * (-b^3*c + b*c^3)^2 + (4 : ℝ) * (1) * (-a^3*c + a*b^2*c + a*c^3)^2 + (4 : ℝ) * (1) * (-a^3*b + a*b^3 + a*b*c^2)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2)^4 - a^8 - b^8 - c^8 ≥ 14 * b^2 * c^2 * (b^2 * c^2 + 4 * a^4)) := @solution
#print axioms solution
