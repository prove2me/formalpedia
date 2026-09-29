-- Prove2me | solution 1 for WorkbookSource.base_5719
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:37:48.982837+00:00
-- url     : https://prove2.me/submissions/04ebf902-2c48-4ed7-9413-05b314f3c0ef

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a - b + c) ^ 2 / (a ^ 2 + (b + c) ^ 2) + (b - c + a) ^ 2 / (b ^ 2 + (c + a) ^ 2) + (c - a + b) ^ 2 / (c ^ 2 + (a + b) ^ 2) ≤ 3  := by
  have hn : 0 ≤ (4*a^5*b + 4*a^5*c + 20*a^4*b*c + 8*a^3*b^3 + 32*a^3*b^2*c + 16*a^3*b*c^2 + 8*a^3*c^3 + 16*a^2*b^3*c + 48*a^2*b^2*c^2 + 32*a^2*b*c^3 + 4*a*b^5 + 20*a*b^4*c + 32*a*b^3*c^2 + 16*a*b^2*c^3 + 20*a*b*c^4 + 4*a*c^5 + 4*b^5*c + 8*b^3*c^3 + 4*b*c^5) := by positivity
  field_simp (disch := positivity)
  nlinarith only [hn]

example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (a - b + c) ^ 2 / (a ^ 2 + (b + c) ^ 2) + (b - c + a) ^ 2 / (b ^ 2 + (c + a) ^ 2) + (c - a + b) ^ 2 / (c ^ 2 + (a + b) ^ 2) ≤ 3) := @solution
#print axioms solution
