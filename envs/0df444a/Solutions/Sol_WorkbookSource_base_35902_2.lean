-- Prove2me | solution 2 for WorkbookSource.base_35902
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T05:13:42.516875+00:00
-- url     : https://prove2.me/submissions/23aac7f2-9df6-47d6-bb08-5e78967eb656

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Real Nat

set_option maxHeartbeats 2000000 in
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (c / (a + b) + b / (a + c) + a / (b + c)) ≤ (3 / 2) * (a / b + b / c + c / a - 2) := by
  rw [← sub_nonneg]
  have key : ((3 / 2) * (a / b + b / c + c / a - 2)) - ((c / (a + b) + b / (a + c) + a / (b + c))) = (a^4*b*c + 3*a^4*c^2 + 3*a^3*b^3 - 2*a^3*b^2*c - 2*a^3*b*c^2 + 3*a^3*c^3 + 3*a^2*b^4 - 2*a^2*b^3*c - 9*a^2*b^2*c^2 - 2*a^2*b*c^3 + a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 + a*b*c^4 + 3*b^3*c^3 + 3*b^2*c^4) / (2*a*b*c*(a + b)*(a + c)*(b + c)) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · have e : (a^4*b*c + 3*a^4*c^2 + 3*a^3*b^3 - 2*a^3*b^2*c - 2*a^3*b*c^2 + 3*a^3*c^3 + 3*a^2*b^4 - 2*a^2*b^3*c - 9*a^2*b^2*c^2 - 2*a^2*b*c^3 + a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 + a*b*c^4 + 3*b^3*c^3 + 3*b^2*c^4) = (3/2) * (a^3*c) * (-b + c)^2 + (1) * (a^3*b) * (-b + c)^2 + (3/2) * (a*b^2*c) * (-a + c)^2 + (1) * (a*b^3) * (-a + c)^2 + (2) * (b*c^3) * (-a + b)^2 + (1/2) * (a*c^3) * (-a + b)^2 + (3/2) * (b^2) * (-a*b + c^2)^2 + (1) * (a*b) * (-a*b + c^2)^2 + (3/2) * (c^2) * (-a^2 + b*c)^2 + (1) * (b*c) * (-a^2 + b*c)^2 + (1) * (a*c) * (-a*c + b^2)^2 + (3/2) * (a^2) * (-a*c + b^2)^2 := by
      ring
    rw [e]
    positivity
  · positivity
