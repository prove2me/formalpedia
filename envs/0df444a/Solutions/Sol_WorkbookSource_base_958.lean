-- Prove2me | solution 1 for WorkbookSource.base_958
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:46:26.673898+00:00
-- url     : https://prove2.me/submissions/35d84382-a316-41ca-90eb-a87c4da583b2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 2) : (a + b - a * b) * (b + c - b * c) * (c + a - c * a) ≤ 1 - a * b * c  := by
  have helim : c = (-a - b + 2) := by linarith only [hab]
  have hsum : 0 ≤ (9 : ℝ) * (-a^2*b/3 + a^2/3 - a*b^2/3 + a*b - 2*a/3 + b^2/3 - 2*b/3 + 1/3)^2 := by positivity
  have hid : ( 1 - a * b * c  ) - ( (a + b - a * b) * (b + c - b * c) * (c + a - c * a) ) = (9 : ℝ) * (-a^2*b/3 + a^2/3 - a*b^2/3 + a*b - 2*a/3 + b^2/3 - 2*b/3 + 1/3)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 2), (a + b - a * b) * (b + c - b * c) * (c + a - c * a) ≤ 1 - a * b * c) := @solution
#print axioms solution
