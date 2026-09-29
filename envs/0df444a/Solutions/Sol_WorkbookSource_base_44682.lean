-- Prove2me | solution 1 for WorkbookSource.base_44682
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:49:59.944525+00:00
-- url     : https://prove2.me/submissions/04c9aede-d55d-4960-9d6d-5768fa3ca3f8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (1 / 4) * (a + b + c + d) ^ 2 ≥ a * c + b * d + (a * b * c ^ 2 + b * c * d ^ 2 + a ^ 2 * c * d + b ^ 2 * a * d) / (a * c + b * d)  := by
  have hn : 0 ≤ (a^3*c + 2*a^2*b*c + a^2*b*d - 2*a^2*c^2 - 2*a^2*c*d + a*b^2*c - 2*a*b^2*d - 2*a*b*c^2 - 4*a*b*c*d + 2*a*b*d^2 + a*c^3 + 2*a*c^2*d + a*c*d^2 + b^3*d + 2*b^2*c*d - 2*b^2*d^2 + b*c^2*d - 2*b*c*d^2 + b*d^3) := by
    have hs0 : 0 ≤ (1 : ℝ) * (b*d) * (a - b - c + d)^2 := by positivity
    have hs1 : 0 ≤ (1 : ℝ) * (a*c) * (-a - b + c + d)^2 := by positivity
    nlinarith only [hs0, hs1]
  have hd : (0 : ℝ) < (4*a*c + 4*b*d) := by positivity
  have heqrat : ( (1 / 4) * (a + b + c + d) ^ 2 ) - ( a * c + b * d + (a * b * c ^ 2 + b * c * d ^ 2 + a ^ 2 * c * d + b ^ 2 * a * d) / (a * c + b * d)  ) = (a^3*c + 2*a^2*b*c + a^2*b*d - 2*a^2*c^2 - 2*a^2*c*d + a*b^2*c - 2*a*b^2*d - 2*a*b*c^2 - 4*a*b*c*d + 2*a*b*d^2 + a*c^3 + 2*a*c^2*d + a*c*d^2 + b^3*d + 2*b^2*c*d - 2*b^2*d^2 + b*c^2*d - 2*b*c*d^2 + b*d^3) / (4*a*c + 4*b*d) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (1 / 4) * (a + b + c + d) ^ 2 ≥ a * c + b * d + (a * b * c ^ 2 + b * c * d ^ 2 + a ^ 2 * c * d + b ^ 2 * a * d) / (a * c + b * d)) := @solution
#print axioms solution
