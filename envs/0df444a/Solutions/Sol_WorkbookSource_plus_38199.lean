-- Prove2me | solution 1 for WorkbookSource.plus_38199
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:46.22985+00:00
-- url     : https://prove2.me/submissions/d9836bab-6169-46ab-a8f3-0713c740e939

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b * c + (a + b) * (b + c) * (c + a))^2 ≤ 3 * (a^2 + b^2 + c^2)^3   := by
  have h0 : 0 ≤ (7/2 : ℝ) * (1) * (-9*a^3/14 + a^2*b/7 - a^2*c/2 - a*b^2/2 - 2*a*c^2/7 + 9*b^3/14 + b^2*c/7 + b*c^2)^2 := by positivity
  have h1 : 0 ≤ (24/7 : ℝ) * (1) * (-9*a^3/16 - 17*a^2*b/32 + 7*a^2*c/32 - 7*a*b^2/32 - 15*a*c^2/32 - 3*b^3/32 + b^2*c + 21*c^3/32)^2 := by positivity
  have h2 : 0 ≤ (315/128 : ℝ) * (1) * (2*a^3/7 - a^2*b + a^2*c/7 - a*b^2/7 + a*c^2 - 5*b^3/7 + 3*c^3/7)^2 := by positivity
  have h3 : 0 ≤ (135/56 : ℝ) * (1) * (a^3/3 - a^2*c + a*b^2 + b^3/3 - 2*c^3/3)^2 := by positivity
  nlinarith only [h0, h1, h2, h3]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b * c + (a + b) * (b + c) * (c + a))^2 ≤ 3 * (a^2 + b^2 + c^2)^3) := @solution
#print axioms solution
