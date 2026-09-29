-- Prove2me | solution 1 for WorkbookSource.base_4186
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:47:40.104645+00:00
-- url     : https://prove2.me/submissions/d9f5c9e9-dea9-476e-af17-1753d9fb9fa5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a^3 + b^3 + c^3 ≥ 3 * (a^3 * c + b^3 * a + c^3 * b)  := by
  have helim : c = (-a - b + 1) := by linarith only [habc]
  have hsum : 0 ≤ (12 : ℝ) * (a^2/4 + a*b - a/2 + b^2/4 - 3*b/4 + 1/4)^2 + (9/4 : ℝ) * (a^2 - b^2 + b - 1/3)^2 := by positivity
  have hid : ( a^3 + b^3 + c^3 ) - ( 3 * (a^3 * c + b^3 * a + c^3 * b)  ) = (12 : ℝ) * (a^2/4 + a*b - a/2 + b^2/4 - 3*b/4 + 1/4)^2 + (9/4 : ℝ) * (a^2 - b^2 + b - 1/3)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1), a^3 + b^3 + c^3 ≥ 3 * (a^3 * c + b^3 * a + c^3 * b)) := @solution
#print axioms solution
