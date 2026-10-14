-- Prove2me | solution 2 for WorkbookSource.base_29201
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T05:14:05.453678+00:00
-- url     : https://prove2.me/submissions/6473a4f6-2346-49eb-a900-27f2fe7b0cf4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Real Nat

set_option maxHeartbeats 2000000 in
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^4 / (3 * a + b + c) + b^4 / (3 * b + c + a) + c^4 / (3 * c + a + b)) ≥ (a^3 + b^3 + c^3) / 5 := by
  rw [ge_iff_le, ← sub_nonneg]
  have key : ((a^4 / (3 * a + b + c) + b^4 / (3 * b + c + a) + c^4 / (3 * c + a + b))) - ((a^3 + b^3 + c^3) / 5) = (2*a^6 + 7*a^5*b + 7*a^5*c + 2*a^4*b^2 + 12*a^4*b*c + 2*a^4*c^2 - 6*a^3*b^3 - 13*a^3*b^2*c - 13*a^3*b*c^2 - 6*a^3*c^3 + 2*a^2*b^4 - 13*a^2*b^3*c - 13*a^2*b*c^3 + 2*a^2*c^4 + 7*a*b^5 + 12*a*b^4*c - 13*a*b^3*c^2 - 13*a*b^2*c^3 + 12*a*b*c^4 + 7*a*c^5 + 2*b^6 + 7*b^5*c + 2*b^4*c^2 - 6*b^3*c^3 + 2*b^2*c^4 + 7*b*c^5 + 2*c^6) / (5*(a + b + 3*c)*(a + 3*b + c)*(3*a + b + c)) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · have e : (2*a^6 + 7*a^5*b + 7*a^5*c + 2*a^4*b^2 + 12*a^4*b*c + 2*a^4*c^2 - 6*a^3*b^3 - 13*a^3*b^2*c - 13*a^3*b*c^2 - 6*a^3*c^3 + 2*a^2*b^4 - 13*a^2*b^3*c - 13*a^2*b*c^3 + 2*a^2*c^4 + 7*a*b^5 + 12*a*b^4*c - 13*a*b^3*c^2 - 13*a*b^2*c^3 + 12*a*b*c^4 + 7*a*c^5 + 2*b^6 + 7*b^5*c + 2*b^4*c^2 - 6*b^3*c^3 + 2*b^2*c^4 + 7*b*c^5 + 2*c^6) = (3/2) * (b^2*c^2) * (-b + c)^2 + (3/2) * (a^2*c^2) * (-a + c)^2 + (1/2) * (a^2*b^2) * (-a + b)^2 + (1) * (b*c) * (-b^2 + c^2)^2 + (6) * (a*c) * (-b^2 + c^2)^2 + (6) * (a*b) * (-b^2 + c^2)^2 + (1/2) * (b^2) * (-a*b + c^2)^2 + (1/2) * (a^2) * (-a*b + c^2)^2 + (6) * (b*c) * (-a^2 + c^2)^2 + (1) * (a*c) * (-a^2 + c^2)^2 + (6) * (a*b) * (-a^2 + c^2)^2 + (1/2) * (b^2) * (-a^2 + b*c)^2 + (1/2) * (a^2) * (-a*c + b^2)^2 + (6) * (b*c) * (-a^2 + b^2)^2 + (6) * (a*c) * (-a^2 + b^2)^2 + (1) * (a*b) * (-a^2 + b^2)^2 + (1/2) * (1) * (-b^3 + c^3)^2 + (1/2) * (1) * (-a*b^2 + c^3)^2 + (1/2) * (1) * (-a^2*b + c^3)^2 + (1/2) * (1) * (-a^3 + c^3)^2 + (3/2) * (1) * (-a^3 + b^3)^2 := by
      ring
    rw [e]
    positivity
  · positivity
