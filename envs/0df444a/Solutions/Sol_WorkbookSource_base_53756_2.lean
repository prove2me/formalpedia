-- Prove2me | solution 2 for WorkbookSource.base_53756
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T05:14:54.682704+00:00
-- url     : https://prove2.me/submissions/e3d5e8a7-56e1-49bb-9322-ffac17a64323

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Real Nat

set_option maxHeartbeats 2000000 in
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 2) : a / b + b / c + c / a + 3 * (a * b + b * c + a * c) ≥ 7 := by
  rw [ge_iff_le, ← sub_nonneg]
  have key : (a / b + b / c + c / a + 3 * (a * b + b * c + a * c)) - (7) = (3*a^2*b^2*c + 3*a^2*b*c^2 + a^2*c + 3*a*b^2*c^2 + a*b^2 - 7*a*b*c + b*c^2) / (a*b*c) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · have e : (3*a^2*b^2*c + 3*a^2*b*c^2 + a^2*c + 3*a*b^2*c^2 + a*b^2 - 7*a*b*c + b*c^2) = (41/4224) * (b*c^2) * (a + b - 2*c)^2 + (25/176) * (a^2*c) * (a - 2*b + c)^2 + (17/528) * (b*c^2) * (-2*a + b + c)^2 + (23/1408) * (b) * (a*b - 2*b*c + c^2)^2 + (25/176) * (a) * (a*c + b^2 - 2*b*c)^2 + (19/176) * (c) * (a*b + a*c - 2*b*c)^2 + (1/88) * (a) * (a*c - 2*b^2 + b*c)^2 + (229/1408) * (b) * (a*b - 2*a*c + c^2)^2 + (201/1408) * (b) * (-2*a*b + a*c + b*c)^2 + (19/176) * (c) * (a^2 - 2*a*b + b*c)^2 + (1/16) * (a) * (-2*a*b + a*c + b^2)^2 := by
      have hc' : c = 2 - a - b := by linarith
      subst hc'
      ring
    rw [e]
    positivity
  · positivity
