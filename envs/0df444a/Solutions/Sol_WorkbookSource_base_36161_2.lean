-- Prove2me | solution 2 for WorkbookSource.base_36161
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T05:13:50.008748+00:00
-- url     : https://prove2.me/submissions/63e493e4-f4de-4327-895e-dd08a1946e86

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Real Nat

set_option maxHeartbeats 2000000 in
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^3 / b^2 + b^3 / c^2 + c^3 / a^2 ≥ a^2 + b^2 + c^2 := by
  rw [ge_iff_le, ← sub_nonneg]
  have key : (a^3 / b^2 + b^3 / c^2 + c^3 / a^2) - (a^2 + b^2 + c^2) = (a^5*c^2 - a^4*b^2*c^2 + a^2*b^5 - a^2*b^4*c^2 - a^2*b^2*c^4 + b^2*c^5) / (a^2*b^2*c^2) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · have e : (a^5*c^2 - a^4*b^2*c^2 + a^2*b^5 - a^2*b^4*c^2 - a^2*b^2*c^4 + b^2*c^5) = (1/9) * (a*b^2*c^3) * (-b + c)^2 + (2/9) * (a^2*b^3*c) * (-b + c)^2 + (2/9) * (a*b^2*c^3) * (-a + c)^2 + (1/9) * (a^3*b*c^2) * (-a + c)^2 + (1/9) * (a^2*b^3*c) * (-a + b)^2 + (2/9) * (a^3*b*c^2) * (-a + b)^2 + (1/9) * (a^2*b^2) * (-b^2 + c^2)^2 + (1/9) * (a^3*b) * (-b^2 + c^2)^2 + (2/9) * (a*b^3) * (-a*b + c^2)^2 + (1/9) * (b^2*c^2) * (-a^2 + c^2)^2 + (1/9) * (b^3*c) * (-a^2 + c^2)^2 + (2/9) * (b*c^3) * (-a^2 + b*c)^2 + (2/9) * (a^3*c) * (-a*c + b^2)^2 + (1/9) * (a*c^3) * (-a^2 + b^2)^2 + (1/9) * (a^2*c^2) * (-a^2 + b^2)^2 + (1/9) * (b^2) * (-a*b^2 + c^3)^2 + (1/9) * (c^2) * (-a^3 + b*c^2)^2 + (1/9) * (a^2) * (-a^2*c + b^3)^2 := by
      have hc' : c = 3 - a - b := by linarith
      subst hc'
      ring
    rw [e]
    positivity
  · positivity
