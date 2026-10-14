-- Prove2me | solution 2 for WorkbookSource.plus_11955
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T05:14:25.06461+00:00
-- url     : https://prove2.me/submissions/11fbcb0f-1d8a-44ce-b91f-38a0e8013aa0

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Real Nat

set_option maxHeartbeats 2000000 in
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a - b) ^ 2 / (a * b) + (b - c) ^ 2 / (b * c) + (c - a) ^ 2 / (c * a) + c / a + a / b + b / c ≥ (3 * b * c + a * c - a * b) / (2 * a * b + a * c) + (3 * a * c + a * b - b * c) / (2 * b * c + a * b) + (3 * a * b + b * c - a * c) / (2 * a * c + b * c) := by
  rw [ge_iff_le, ← sub_nonneg]
  have key : ((a - b) ^ 2 / (a * b) + (b - c) ^ 2 / (b * c) + (c - a) ^ 2 / (c * a) + c / a + a / b + b / c) - ((3 * b * c + a * c - a * b) / (2 * a * b + a * c) + (3 * a * c + a * b - b * c) / (2 * b * c + a * b) + (3 * a * b + b * c - a * c) / (2 * a * c + b * c)) = (4*a^4*b^2 + 10*a^4*b*c + 4*a^4*c^2 + 4*a^3*b^3 - 10*a^3*b^2*c - a^3*b*c^2 + 4*a^3*c^3 + 4*a^2*b^4 - a^2*b^3*c - 33*a^2*b^2*c^2 - 10*a^2*b*c^3 + 4*a^2*c^4 + 10*a*b^4*c - 10*a*b^3*c^2 - a*b^2*c^3 + 10*a*b*c^4 + 4*b^4*c^2 + 4*b^3*c^3 + 4*b^2*c^4) / (a*b*c*(a + 2*c)*(2*a + b)*(2*b + c)) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · have e : (4*a^4*b^2 + 10*a^4*b*c + 4*a^4*c^2 + 4*a^3*b^3 - 10*a^3*b^2*c - a^3*b*c^2 + 4*a^3*c^3 + 4*a^2*b^4 - a^2*b^3*c - 33*a^2*b^2*c^2 - 10*a^2*b*c^3 + 4*a^2*c^4 + 10*a*b^4*c - 10*a*b^3*c^2 - a*b^2*c^3 + 10*a*b*c^4 + 4*b^4*c^2 + 4*b^3*c^3 + 4*b^2*c^4) = (9/10) * (b^2*c^2) * (-b + c)^2 + (24/5) * (a*b^2*c) * (-b + c)^2 + (6) * (a*b*c^2) * (-a + c)^2 + (12/5) * (a^2*b*c) * (-a + c)^2 + (6/5) * (a*b^2*c) * (-a + b)^2 + (9/5) * (a^2*b*c) * (-a + b)^2 + (1/5) * (b^2) * (-a*b + c^2)^2 + (4) * (a*b) * (-a*b + c^2)^2 + (11/10) * (a^2) * (-a*b + c^2)^2 + (27/10) * (b^2) * (-a^2 + c^2)^2 + (1/5) * (c^2) * (-a^2 + b*c)^2 + (29/5) * (b*c) * (-a^2 + b*c)^2 + (1/5) * (b^2) * (-a^2 + b*c)^2 + (29/10) * (c^2) * (-a*c + b^2)^2 + (4) * (a*c) * (-a*c + b^2)^2 + (19/5) * (a^2) * (-a*c + b^2)^2 := by
      ring
    rw [e]
    positivity
  · positivity
