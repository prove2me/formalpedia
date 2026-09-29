-- Prove2me | solution 1 for WorkbookSource.base_30815
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:07.41673+00:00
-- url     : https://prove2.me/submissions/940daeaf-b64e-41b3-af68-555412e97ec2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + b + c = 3) : 3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 16 * (a * b + b * c + c * a) ≤ 57  := by
  have helim : c = (-a - b + 3) := by linarith only [h]
  have hsum : 0 ≤ (73 : ℝ) * (-27*a^2/146 - 24*a*b/73 + a + 3*b^2/146 + 55*b/146 - 129/146)^2 + (2523/292 : ℝ) * (7*a^2/29 - 20*a*b/29 - 17*b^2/29 + b + 1/29)^2 := by positivity
  have hid : ( 57  ) - ( 3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 16 * (a * b + b * c + c * a) ) = (73 : ℝ) * (-27*a^2/146 - 24*a*b/73 + a + 3*b^2/146 + 55*b/146 - 129/146)^2 + (2523/292 : ℝ) * (7*a^2/29 - 20*a*b/29 - 17*b^2/29 + b + 1/29)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + b + c = 3), 3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 16 * (a * b + b * c + c * a) ≤ 57) := @solution
#print axioms solution
