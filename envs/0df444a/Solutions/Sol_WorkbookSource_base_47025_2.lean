-- Prove2me | solution 2 for WorkbookSource.base_47025
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T05:13:46.88922+00:00
-- url     : https://prove2.me/submissions/f337af1c-fbd2-4795-a00b-40f21bf789a1

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Real Nat

set_option maxHeartbeats 2000000 in
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (5 / (2 * a + b) + 4 / (2 * b + c) + 3 / (2 * c + a)) ≥ (12 / (3 * a + 2 * b + c) + 8 / (a + 3 * b + 2 * c) + 4 / (2 * a + b + 3 * c)) := by
  rw [ge_iff_le, ← sub_nonneg]
  have key : ((5 / (2 * a + b) + 4 / (2 * b + c) + 3 / (2 * c + a))) - ((12 / (3 * a + 2 * b + c) + 8 / (a + 3 * b + 2 * c) + 4 / (2 * a + b + 3 * c))) = (48*a^5 + 20*a^4*b + 178*a^4*c - 34*a^3*b^2 - 33*a^3*b*c + 145*a^3*c^2 + 124*a^2*b^3 - 270*a^2*b^2*c - 297*a^2*b*c^2 - 55*a^2*c^3 + 142*a*b^4 - 3*a*b^3*c - 297*a*b^2*c^2 - 108*a*b*c^3 - 4*a*c^4 + 36*b^5 + 32*b^4*c - 43*b^3*c^2 + 151*b^2*c^3 + 208*b*c^4 + 60*c^5) / ((a + 2*c)*(2*a + b)*(2*b + c)*(a + 3*b + 2*c)*(2*a + b + 3*c)*(3*a + 2*b + c)) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · have e : (48*a^5 + 20*a^4*b + 178*a^4*c - 34*a^3*b^2 - 33*a^3*b*c + 145*a^3*c^2 + 124*a^2*b^3 - 270*a^2*b^2*c - 297*a^2*b*c^2 - 55*a^2*c^3 + 142*a*b^4 - 3*a*b^3*c - 297*a*b^2*c^2 - 108*a*b*c^3 - 4*a*c^4 + 36*b^5 + 32*b^4*c - 43*b^3*c^2 + 151*b^2*c^3 + 208*b*c^4 + 60*c^5) = (19/2) * (a^3) * (-b + c)^2 + (2) * (c^3) * (-a + c)^2 + (49/2) * (b*c^2) * (-a + c)^2 + (65/4) * (a^3) * (-a + c)^2 + (1) * (b^2*c) * (-a + b)^2 + (2) * (a^3) * (-a + b)^2 + (43/2) * (b) * (-b^2 + c^2)^2 + (59/2) * (c) * (-a*b + c^2)^2 + (152) * (b) * (-a*b + c^2)^2 + (57/2) * (c) * (-a^2 + c^2)^2 + (10) * (b) * (-a^2 + c^2)^2 + (151) * (c) * (-a^2 + b*c)^2 + (7) * (a) * (-a^2 + b*c)^2 + (1/2) * (b) * (-a*c + b^2)^2 + (477/4) * (a) * (-a*c + b^2)^2 + (31) * (c) * (-a^2 + b^2)^2 + (14) * (b) * (-a^2 + b^2)^2 + (91/4) * (a) * (-a^2 + b^2)^2 := by
      ring
    rw [e]
    positivity
  · positivity
