-- Prove2me | solution 1 for WorkbookSource.plus_40795
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:41:25.33829+00:00
-- url     : https://prove2.me/submissions/c3a3c0cf-2f59-499d-88ce-0179a0118719

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a + b + c = 3) : 6 * (a ^ 4 + b ^ 4 + c ^ 4) - 4 * (a ^ 3 * c + b ^ 3 * a + c ^ 3 * b) - 37 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 91 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - 56 * (a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b) ≥ 0   := by
  have hw0 : 0 ≤ (a + b + c - 3) := by linarith only [ha]
  have hw1 : 0 ≤ (-a - b - c + 3) := by linarith only [ha]
  have hsum : 0 ≤ (1190/13 : ℝ) * (1) * (23*a^2/140 - 1119*a*b/2380 - 1119*a*c/2380 - 481*b^2/2380 + b*c - 13*c^2/595)^2 + (339403/4760 : ℝ) * (1) * (313769*a^2/4412239 - 1119*a*b/1261 + a*c + 392341*b^2/4412239 - 92536*c^2/339403)^2 + (248429/16393 : ℝ) * (1) * (-1600*a^2/3499 + a*b - 1171*b^2/3499 - 728*c^2/3499)^2 := by positivity
  have hid : ( 6 * (a ^ 4 + b ^ 4 + c ^ 4) - 4 * (a ^ 3 * c + b ^ 3 * a + c ^ 3 * b) - 37 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 91 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - 56 * (a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b) ) - ( 0   ) = (1190/13 : ℝ) * (1) * (23*a^2/140 - 1119*a*b/2380 - 1119*a*c/2380 - 481*b^2/2380 + b*c - 13*c^2/595)^2 + (339403/4760 : ℝ) * (1) * (313769*a^2/4412239 - 1119*a*b/1261 + a*c + 392341*b^2/4412239 - 92536*c^2/339403)^2 + (248429/16393 : ℝ) * (1) * (-1600*a^2/3499 + a*b - 1171*b^2/3499 - 728*c^2/3499)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a + b + c = 3), 6 * (a ^ 4 + b ^ 4 + c ^ 4) - 4 * (a ^ 3 * c + b ^ 3 * a + c ^ 3 * b) - 37 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 91 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - 56 * (a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b) ≥ 0) := @solution
#print axioms solution
