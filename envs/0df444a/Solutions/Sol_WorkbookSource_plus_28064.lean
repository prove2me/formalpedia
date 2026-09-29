-- Prove2me | solution 1 for WorkbookSource.plus_28064
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:11.306914+00:00
-- url     : https://prove2.me/submissions/428818d0-e5c0-4631-97ec-0c14ddfbfa17

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) + (1 + a * b * c) * (a^2 + b^2 + c^2) + a * b * c ≥ 15   := by
  have helim : c = (-a - b + 3) := by linarith only [hab]
  have hsum : 0 ≤ (16 : ℝ) * (-a^2*b/4 + a^2/4 - a*b^2/4 + a*b - 3*a/4 + b^2/4 - 3*b/4 + 1/2)^2 := by positivity
  have hid : ( (a^2 + 1) * (b^2 + 1) * (c^2 + 1) + (1 + a * b * c) * (a^2 + b^2 + c^2) + a * b * c ) - ( 15   ) = (16 : ℝ) * (-a^2*b/4 + a^2/4 - a*b^2/4 + a*b - 3*a/4 + b^2/4 - 3*b/4 + 1/2)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3), (a^2 + 1) * (b^2 + 1) * (c^2 + 1) + (1 + a * b * c) * (a^2 + b^2 + c^2) + a * b * c ≥ 15) := @solution
#print axioms solution
