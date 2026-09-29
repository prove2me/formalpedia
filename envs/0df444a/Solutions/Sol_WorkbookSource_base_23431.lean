-- Prove2me | solution 1 for WorkbookSource.base_23431
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:28:30.989872+00:00
-- url     : https://prove2.me/submissions/4bf525c8-6be2-4f02-b3f2-12c7d99cc196

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) :  (a + b) * (b + c) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3 + 1 / 3) ≤ 4 / 27  := by
  have helim : c = (-a - b + 1) := by linarith only [habc]
  have hsum : 0 ≤ (12 : ℝ) * (-a^2*b/2 + a^2/2 - a*b^2/2 + a*b - a/2 + b^2/2 - b/2 + 1/9)^2 := by positivity
  have hid : ( 4 / 27  ) - (  (a + b) * (b + c) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3 + 1 / 3) ) = (12 : ℝ) * (-a^2*b/2 + a^2/2 - a*b^2/2 + a*b - a/2 + b^2/2 - b/2 + 1/9)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1), (a + b) * (b + c) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3 + 1 / 3) ≤ 4 / 27) := @solution
#print axioms solution
