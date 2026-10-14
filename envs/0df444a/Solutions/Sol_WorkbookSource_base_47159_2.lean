-- Prove2me | solution 2 for WorkbookSource.base_47159
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T05:13:47.429418+00:00
-- url     : https://prove2.me/submissions/6308dc9a-db21-4e0a-a3ee-40703bab7b15

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Real Nat

set_option maxHeartbeats 2000000 in
theorem solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 2 * b^2) * (b^2 + 2 * c^2) * (c^2 + 2 * a^2) ≥ 1/3 * (a * b + b * c + c * a)^2 * (a + b + c)^2 := by
  rw [ge_iff_le, ← sub_nonneg]
  have key : ((a^2 + 2 * b^2) * (b^2 + 2 * c^2) * (c^2 + 2 * a^2)) - (1/3 * (a * b + b * c + c * a)^2 * (a + b + c)^2) = (5*a^4*b^2 - 2*a^4*b*c + 11*a^4*c^2 - 2*a^3*b^3 - 8*a^3*b^2*c - 8*a^3*b*c^2 - 2*a^3*c^3 + 11*a^2*b^4 - 8*a^2*b^3*c + 12*a^2*b^2*c^2 - 8*a^2*b*c^3 + 5*a^2*c^4 - 2*a*b^4*c - 8*a*b^3*c^2 - 8*a*b^2*c^3 - 2*a*b*c^4 + 5*b^4*c^2 - 2*b^3*c^3 + 11*b^2*c^4) / (3) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · have e : (5*a^4*b^2 - 2*a^4*b*c + 11*a^4*c^2 - 2*a^3*b^3 - 8*a^3*b^2*c - 8*a^3*b*c^2 - 2*a^3*c^3 + 11*a^2*b^4 - 8*a^2*b^3*c + 12*a^2*b^2*c^2 - 8*a^2*b*c^3 + 5*a^2*c^4 - 2*a*b^4*c - 8*a*b^3*c^2 - 8*a*b^2*c^3 - 2*a*b*c^4 + 5*b^4*c^2 - 2*b^3*c^3 + 11*b^2*c^4) = (1) * (b^2*c^2) * (-b + c)^2 + (4) * (a^2*b^2) * (-b + c)^2 + (1) * (a^4) * (-b + c)^2 + (4) * (b^2*c^2) * (-a + c)^2 + (1) * (b^4) * (-a + c)^2 + (1) * (a^2*c^2) * (-a + c)^2 + (1) * (c^4) * (-a + b)^2 + (3) * (b^2*c^2) * (-a + b)^2 + (1) * (a^2*c^2) * (-a + b)^2 + (1) * (a^2*b^2) * (-a + b)^2 + (1) * (b^2) * (-a*b + c^2)^2 + (3) * (a^2) * (-a*b + c^2)^2 + (4) * (c^2) * (-a^2 + b*c)^2 + (4) * (a^2) * (-a*c + b^2)^2 := by
      ring
    rw [e]
    positivity
  · positivity
