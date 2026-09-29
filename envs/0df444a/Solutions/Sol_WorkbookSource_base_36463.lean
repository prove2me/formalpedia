-- Prove2me | solution 1 for WorkbookSource.base_36463
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:28:20.939518+00:00
-- url     : https://prove2.me/submissions/5e6f209c-3ff7-4f64-ab81-b62e89249533

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution {a b c : ℝ} : (a^2 * b^2 + b^2 * c^2 + c^2 * a^2 - a * b * c * (a + b + c)) * (a^4 + b^4 + c^4 - (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)) ≥ 3 / 4 * (a^3 * b + b^3 * c + c^3 * a - a * b * c * (a + b + c))^2  := by
  have hsum : 0 ≤ (1 : ℝ) * (-a^3*b/2 + a^3*c - a^2*b*c/2 + a*b^3 - a*b^2*c/2 - a*b*c^2/2 - a*c^3/2 - b^3*c/2 + b*c^3)^2 := by positivity
  have hid : ( (a^2 * b^2 + b^2 * c^2 + c^2 * a^2 - a * b * c * (a + b + c)) * (a^4 + b^4 + c^4 - (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)) ) - ( 3 / 4 * (a^3 * b + b^3 * c + c^3 * a - a * b * c * (a + b + c))^2  ) = (1 : ℝ) * (-a^3*b/2 + a^3*c - a^2*b*c/2 + a*b^3 - a*b^2*c/2 - a*b*c^2/2 - a*c^3/2 - b^3*c/2 + b*c^3)^2 := by ring
  linarith only [hsum, hid]
example : (∀ {a b c : ℝ}, (a^2 * b^2 + b^2 * c^2 + c^2 * a^2 - a * b * c * (a + b + c)) * (a^4 + b^4 + c^4 - (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)) ≥ 3 / 4 * (a^3 * b + b^3 * c + c^3 * a - a * b * c * (a + b + c))^2) := @solution
#print axioms solution
