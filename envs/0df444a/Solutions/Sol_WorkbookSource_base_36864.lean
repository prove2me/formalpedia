-- Prove2me | solution 1 for WorkbookSource.base_36864
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:28:21.55854+00:00
-- url     : https://prove2.me/submissions/a3b0b579-99b0-4023-8141-193cacf01551

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution {a b c : ℝ} : (a^4 * b^2 + a^2 * b^4 + b^4 * c^2 + b^2 * c^4 + c^4 * a^2 + c^2 * a^4 + 2 * a^2 * b^2 * c^2) * (b^2 + a^2 + c^2 + b^2 + a^2 + c^2 + 2) ≥ (2 * (a^2 * b^2 + b^2 * c^2 + a^2 * c^2) + 2 * a * b * c)^2  := by
  have hsum : 0 ≤ (2 : ℝ) * (-a^3*c + b*c^2)^2 + (2 : ℝ) * (-a*b^2 + b*c^3)^2 + (2 : ℝ) * (-a^3*b + b^2*c)^2 + (2 : ℝ) * (-a*c^2 + b^3*c)^2 + (2 : ℝ) * (-a^2*b + a*c^3)^2 + (2 : ℝ) * (-a^2*c + a*b^3)^2 := by positivity
  have hid : ( (a^4 * b^2 + a^2 * b^4 + b^4 * c^2 + b^2 * c^4 + c^4 * a^2 + c^2 * a^4 + 2 * a^2 * b^2 * c^2) * (b^2 + a^2 + c^2 + b^2 + a^2 + c^2 + 2) ) - ( (2 * (a^2 * b^2 + b^2 * c^2 + a^2 * c^2) + 2 * a * b * c)^2  ) = (2 : ℝ) * (-a^3*c + b*c^2)^2 + (2 : ℝ) * (-a*b^2 + b*c^3)^2 + (2 : ℝ) * (-a^3*b + b^2*c)^2 + (2 : ℝ) * (-a*c^2 + b^3*c)^2 + (2 : ℝ) * (-a^2*b + a*c^3)^2 + (2 : ℝ) * (-a^2*c + a*b^3)^2 := by ring
  linarith only [hsum, hid]
example : (∀ {a b c : ℝ}, (a^4 * b^2 + a^2 * b^4 + b^4 * c^2 + b^2 * c^4 + c^4 * a^2 + c^2 * a^4 + 2 * a^2 * b^2 * c^2) * (b^2 + a^2 + c^2 + b^2 + a^2 + c^2 + 2) ≥ (2 * (a^2 * b^2 + b^2 * c^2 + a^2 * c^2) + 2 * a * b * c)^2) := @solution
#print axioms solution
