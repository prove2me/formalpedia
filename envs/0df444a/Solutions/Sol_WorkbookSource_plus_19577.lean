-- Prove2me | solution 1 for WorkbookSource.plus_19577
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:28:55.489296+00:00
-- url     : https://prove2.me/submissions/82f4c72b-5e81-4696-8f22-7ccadba8b4c0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (a b c : ℝ) : (b - c) ^ 2 * c ^ 2 * ((a - b) ^ 2 * (a ^ 4 + 2 * a ^ 3 * b + 6 * a ^ 2 * b ^ 2 + 2 * a * b ^ 3 + b ^ 4 - 2 * c ^ 2 * (a + b) ^ 2) + c ^ 4 * (a ^ 2 + b ^ 2)) ≥ 0   := by
  have hsum : 0 ≤ (5 : ℝ) * (a^3*b*c/5 - a^3*c^2/5 + 4*a^2*b^2*c/5 - 4*a^2*b*c^2/5 - a*b^3*c + a*b^2*c^2 - a*b*c^3/5 + a*c^4/5)^2 + (9/5 : ℝ) * (4*a^3*b*c/9 - 4*a^3*c^2/9 - a^2*b^2*c + a^2*b*c^2 - 4*a*b*c^3/9 + 4*a*c^4/9 + 5*b^4*c/9 - 5*b^3*c^2/9 - 5*b^2*c^3/9 + 5*b*c^4/9)^2 + (4/9 : ℝ) * (-a^3*b*c + a^3*c^2 + a*b*c^3 - a*c^4 + b^4*c - b^3*c^2 - b^2*c^3 + b*c^4)^2 := by positivity
  have hid : ( (b - c) ^ 2 * c ^ 2 * ((a - b) ^ 2 * (a ^ 4 + 2 * a ^ 3 * b + 6 * a ^ 2 * b ^ 2 + 2 * a * b ^ 3 + b ^ 4 - 2 * c ^ 2 * (a + b) ^ 2) + c ^ 4 * (a ^ 2 + b ^ 2)) ) - ( 0   ) = (5 : ℝ) * (a^3*b*c/5 - a^3*c^2/5 + 4*a^2*b^2*c/5 - 4*a^2*b*c^2/5 - a*b^3*c + a*b^2*c^2 - a*b*c^3/5 + a*c^4/5)^2 + (9/5 : ℝ) * (4*a^3*b*c/9 - 4*a^3*c^2/9 - a^2*b^2*c + a^2*b*c^2 - 4*a*b*c^3/9 + 4*a*c^4/9 + 5*b^4*c/9 - 5*b^3*c^2/9 - 5*b^2*c^3/9 + 5*b*c^4/9)^2 + (4/9 : ℝ) * (-a^3*b*c + a^3*c^2 + a*b*c^3 - a*c^4 + b^4*c - b^3*c^2 - b^2*c^3 + b*c^4)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ), (b - c) ^ 2 * c ^ 2 * ((a - b) ^ 2 * (a ^ 4 + 2 * a ^ 3 * b + 6 * a ^ 2 * b ^ 2 + 2 * a * b ^ 3 + b ^ 4 - 2 * c ^ 2 * (a + b) ^ 2) + c ^ 4 * (a ^ 2 + b ^ 2)) ≥ 0) := @solution
#print axioms solution
