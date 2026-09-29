-- Prove2me | solution 1 for WorkbookSource.base_21853
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:48:01.131129+00:00
-- url     : https://prove2.me/submissions/a3f4f95e-e7ad-4ba6-8959-5a39390f118d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 + b^2 + c^2)^2 ≥ 4 * (a^2 + b^2 + c^2) - a * b * c * (a + b + c)  := by
  have helim : c = (-a - b + 3) := by linarith only [habc]
  have hsum : 0 ≤ (45 : ℝ) * (4*a^2/15 + a*b/3 - 14*a/15 + 4*b^2/15 - 14*b/15 + 1)^2 + (4/5 : ℝ) * (-3*a^2/8 + 3*a/8 - b^2 + b)^2 + (11/16 : ℝ) * (-a^2 + a)^2 := by positivity
  have hid : ( (a^2 + b^2 + c^2)^2 ) - ( 4 * (a^2 + b^2 + c^2) - a * b * c * (a + b + c)  ) = (45 : ℝ) * (4*a^2/15 + a*b/3 - 14*a/15 + 4*b^2/15 - 14*b/15 + 1)^2 + (4/5 : ℝ) * (-3*a^2/8 + 3*a/8 - b^2 + b)^2 + (11/16 : ℝ) * (-a^2 + a)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a^2 + b^2 + c^2)^2 ≥ 4 * (a^2 + b^2 + c^2) - a * b * c * (a + b + c)) := @solution
#print axioms solution
