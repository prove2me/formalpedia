-- Prove2me | solution 1 for WorkbookSource.base_1361
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:25:06.549382+00:00
-- url     : https://prove2.me/submissions/adaaef29-a20d-49c1-b31b-988306b89e1b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (a b c : ℝ) : a^6 * b^2 + 2 * a^6 * b * c + a^6 * c^2 - 2 * a^5 * b^3 - 2 * a^5 * b^2 * c - 2 * a^5 * b * c^2 - 2 * a^5 * c^3 + 2 * a^4 * b^4 + 4 * a^4 * b^2 * c^2 + 2 * a^4 * c^4 - 2 * a^3 * b^5 - 2 * a^3 * b^3 * c^2 - 2 * a^3 * b^2 * c^3 - 2 * a^3 * c^5 + a^2 * b^6 - 2 * a^2 * b^5 * c + 4 * a^2 * b^4 * c^2 - 2 * a^2 * b^3 * c^3 + 4 * a^2 * b^2 * c^4 - 2 * a^2 * b * c^5 + a^2 * c^6 + 2 * a * b^6 * c - 2 * a * b^5 * c^2 - 2 * a * b^2 * c^5 + 2 * a * b * c^6 + b^6 * c^2 - 2 * b^5 * c^3 + 2 * b^4 * c^4 - 2 * b^3 * c^5 + b^2 * c^6 ≥ 0  := by
  have hsum : 0 ≤ (2 : ℝ) * (a^2*b^2/2 + a^2*c^2/2 - a*b^3/2 - a*c^3/2 - b^3*c/2 + b^2*c^2 - b*c^3/2)^2 + (2 : ℝ) * (-a^2*b*c/2 - a*b^2*c/2 + a*b*c^2)^2 + (3/2 : ℝ) * (-a^2*b*c + a*b^2*c)^2 + (3/2 : ℝ) * (-2*a^3*b/3 - 2*a^3*c/3 + a^2*b^2/3 + a^2*c^2 + a*b^3/3 - a*c^3/3 + b^3*c/3 - b*c^3/3)^2 + (4/3 : ℝ) * (-a^3*b/2 - a^3*c/2 + a^2*b^2 - a*b^3/2 + a*c^3/2 - b^3*c/2 + b*c^3/2)^2 := by positivity
  have hid : ( a^6 * b^2 + 2 * a^6 * b * c + a^6 * c^2 - 2 * a^5 * b^3 - 2 * a^5 * b^2 * c - 2 * a^5 * b * c^2 - 2 * a^5 * c^3 + 2 * a^4 * b^4 + 4 * a^4 * b^2 * c^2 + 2 * a^4 * c^4 - 2 * a^3 * b^5 - 2 * a^3 * b^3 * c^2 - 2 * a^3 * b^2 * c^3 - 2 * a^3 * c^5 + a^2 * b^6 - 2 * a^2 * b^5 * c + 4 * a^2 * b^4 * c^2 - 2 * a^2 * b^3 * c^3 + 4 * a^2 * b^2 * c^4 - 2 * a^2 * b * c^5 + a^2 * c^6 + 2 * a * b^6 * c - 2 * a * b^5 * c^2 - 2 * a * b^2 * c^5 + 2 * a * b * c^6 + b^6 * c^2 - 2 * b^5 * c^3 + 2 * b^4 * c^4 - 2 * b^3 * c^5 + b^2 * c^6 ) - ( 0  ) = (2 : ℝ) * (a^2*b^2/2 + a^2*c^2/2 - a*b^3/2 - a*c^3/2 - b^3*c/2 + b^2*c^2 - b*c^3/2)^2 + (2 : ℝ) * (-a^2*b*c/2 - a*b^2*c/2 + a*b*c^2)^2 + (3/2 : ℝ) * (-a^2*b*c + a*b^2*c)^2 + (3/2 : ℝ) * (-2*a^3*b/3 - 2*a^3*c/3 + a^2*b^2/3 + a^2*c^2 + a*b^3/3 - a*c^3/3 + b^3*c/3 - b*c^3/3)^2 + (4/3 : ℝ) * (-a^3*b/2 - a^3*c/2 + a^2*b^2 - a*b^3/2 + a*c^3/2 - b^3*c/2 + b*c^3/2)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ), a^6 * b^2 + 2 * a^6 * b * c + a^6 * c^2 - 2 * a^5 * b^3 - 2 * a^5 * b^2 * c - 2 * a^5 * b * c^2 - 2 * a^5 * c^3 + 2 * a^4 * b^4 + 4 * a^4 * b^2 * c^2 + 2 * a^4 * c^4 - 2 * a^3 * b^5 - 2 * a^3 * b^3 * c^2 - 2 * a^3 * b^2 * c^3 - 2 * a^3 * c^5 + a^2 * b^6 - 2 * a^2 * b^5 * c + 4 * a^2 * b^4 * c^2 - 2 * a^2 * b^3 * c^3 + 4 * a^2 * b^2 * c^4 - 2 * a^2 * b * c^5 + a^2 * c^6 + 2 * a * b^6 * c - 2 * a * b^5 * c^2 - 2 * a * b^2 * c^5 + 2 * a * b * c^6 + b^6 * c^2 - 2 * b^5 * c^3 + 2 * b^4 * c^4 - 2 * b^3 * c^5 + b^2 * c^6 ≥ 0) := @solution
#print axioms solution
