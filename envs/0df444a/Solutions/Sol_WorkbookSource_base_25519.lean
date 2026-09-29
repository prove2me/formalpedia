-- Prove2me | solution 1 for WorkbookSource.base_25519
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:48:02.132307+00:00
-- url     : https://prove2.me/submissions/c1896682-dd33-4928-bc49-ef42e58d3a92

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 3 * (a^3 + b^3 + c^3) ≥ 3 * a * b * c + 2 * (a^3 * c + b^3 * c + a * b * c^2)  := by
  have helim : c = (-a - b + 3) := by linarith only [habc]
  have hsum : 0 ≤ (81 : ℝ) * (-a/2 - b/2 + 1)^2 + (27/4 : ℝ) * (4*a^2/9 - a - 4*b^2/9 + b)^2 + (2/3 : ℝ) * (-a^2 + b^2)^2 := by positivity
  have hid : ( 3 * (a^3 + b^3 + c^3) ) - ( 3 * a * b * c + 2 * (a^3 * c + b^3 * c + a * b * c^2)  ) = (81 : ℝ) * (-a/2 - b/2 + 1)^2 + (27/4 : ℝ) * (4*a^2/9 - a - 4*b^2/9 + b)^2 + (2/3 : ℝ) * (-a^2 + b^2)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), 3 * (a^3 + b^3 + c^3) ≥ 3 * a * b * c + 2 * (a^3 * c + b^3 * c + a * b * c^2)) := @solution
#print axioms solution
