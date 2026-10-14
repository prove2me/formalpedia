-- Prove2me | solution 2 for WorkbookSource.plus_11598
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T05:15:22.525974+00:00
-- url     : https://prove2.me/submissions/729028c4-62c7-4820-bd60-9cfa4503daba

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Real Nat

set_option maxHeartbeats 2000000 in
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^3 + 1)/(a^2 + 1) + (b^3 + 1)/(b^2 + 1) + (c^3 + 1)/(c^2 + 1) ≥ 3 := by
  rw [ge_iff_le, ← sub_nonneg]
  have key : ((a^3 + 1)/(a^2 + 1) + (b^3 + 1)/(b^2 + 1) + (c^3 + 1)/(c^2 + 1)) - (3) = (a^3*b^2*c^2 + a^3*b^2 + a^3*c^2 + a^3 + a^2*b^3*c^2 + a^2*b^3 + a^2*b^2*c^3 - 3*a^2*b^2*c^2 - 2*a^2*b^2 + a^2*c^3 - 2*a^2*c^2 - a^2 + b^3*c^2 + b^3 + b^2*c^3 - 2*b^2*c^2 - b^2 + c^3 - c^2) / ((a^2 + 1)*(b^2 + 1)*(c^2 + 1)) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · have e : (a^3*b^2*c^2 + a^3*b^2 + a^3*c^2 + a^3 + a^2*b^3*c^2 + a^2*b^3 + a^2*b^2*c^3 - 3*a^2*b^2*c^2 - 2*a^2*b^2 + a^2*c^3 - 2*a^2*c^2 - a^2 + b^3*c^2 + b^3 + b^2*c^3 - 2*b^2*c^2 - b^2 + c^3 - c^2) = (7/1053) * (c^5) * (-b + c)^2 + (5/3159) * (b^5) * (-b + c)^2 + (5/3159) * (c^5) * (-a + c)^2 + (5/3159) * (a^5) * (-a + b)^2 + (8/243) * (a*b*c) * (-b^2 + c^2)^2 + (391/9477) * (a^2*c) * (-b^2 + c^2)^2 + (415/9477) * (a^2*b) * (-b^2 + c^2)^2 + (583/9477) * (a^3) * (-b^2 + c^2)^2 + (209/9477) * (b^3) * (-a*b + c^2)^2 + (197/9477) * (a^3) * (-a*b + c^2)^2 + (373/9477) * (b^2*c) * (-a^2 + c^2)^2 + (541/9477) * (b^3) * (-a^2 + c^2)^2 + (8/243) * (a*b*c) * (-a^2 + c^2)^2 + (412/9477) * (a*b^2) * (-a^2 + c^2)^2 + (188/9477) * (c^3) * (-a^2 + b*c)^2 + (113/9477) * (b^3) * (-a^2 + b*c)^2 + (218/9477) * (c^3) * (-a*c + b^2)^2 + (167/9477) * (a^3) * (-a*c + b^2)^2 + (562/9477) * (c^3) * (-a^2 + b^2)^2 + (496/9477) * (b*c^2) * (-a^2 + b^2)^2 + (457/9477) * (a*c^2) * (-a^2 + b^2)^2 + (8/243) * (a*b*c) * (-a^2 + b^2)^2 + (101/3159) * (a) * (-a*b^2 + c^3)^2 + (133/3159) * (b) * (-a^2*b + c^3)^2 + (101/3159) * (b) * (-a^3 + b*c^2)^2 + (7/1053) * (a) * (-a^3 + b*c^2)^2 + (7/243) * (c) * (-a^3 + b^2*c)^2 + (7/243) * (a) * (-a*c^2 + b^3)^2 + (101/3159) * (c) * (-a^2*c + b^3)^2 + (7/1053) * (b) * (-a^2*c + b^3)^2 := by
      have hc' : c = 3 - a - b := by linarith
      subst hc'
      ring
    rw [e]
    positivity
  · positivity
