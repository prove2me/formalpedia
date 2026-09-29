-- Prove2me | solution 1 for WorkbookSource.base_27454
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:48:03.225433+00:00
-- url     : https://prove2.me/submissions/53a07f44-9872-4cb7-9c0e-4b35e34d4304

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 + 3) * (b^2 + 3) * (c^2 + 3) ≥ 4 * (a + b + c + 1)^2  := by
  have helim : c = (-a - b + 3) := by linarith only [habc]
  have hsum : 0 ≤ (44 : ℝ) * (a^2*b/44 + 49*a^2/396 + a*b^2/44 - 13*a*b/198 - 27*a/44 + 49*b^2/396 - 27*b/44 + 1)^2 + (6947/396 : ℝ) * (243*a^2*b/6947 - 481*a^2/6947 + 243*a*b^2/6947 - 2858*a*b/6947 - 1853*a/6947 - 2241*b^2/6947 + b)^2 + (113200/6947 : ℝ) * (27*a^2*b/566 - 4676*a^2/12735 + 27*a*b^2/566 - 1429*a*b/2547 + a - 2129*b^2/12735)^2 + (125840/22923 : ℝ) * (-9*a^2*b/22 - a^2/11 - 9*a*b^2/22 + a*b - b^2/11)^2 := by positivity
  have hid : ( (a^2 + 3) * (b^2 + 3) * (c^2 + 3) ) - ( 4 * (a + b + c + 1)^2  ) = (44 : ℝ) * (a^2*b/44 + 49*a^2/396 + a*b^2/44 - 13*a*b/198 - 27*a/44 + 49*b^2/396 - 27*b/44 + 1)^2 + (6947/396 : ℝ) * (243*a^2*b/6947 - 481*a^2/6947 + 243*a*b^2/6947 - 2858*a*b/6947 - 1853*a/6947 - 2241*b^2/6947 + b)^2 + (113200/6947 : ℝ) * (27*a^2*b/566 - 4676*a^2/12735 + 27*a*b^2/566 - 1429*a*b/2547 + a - 2129*b^2/12735)^2 + (125840/22923 : ℝ) * (-9*a^2*b/22 - a^2/11 - 9*a*b^2/22 + a*b - b^2/11)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a^2 + 3) * (b^2 + 3) * (c^2 + 3) ≥ 4 * (a + b + c + 1)^2) := @solution
#print axioms solution
