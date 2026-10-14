-- Prove2me | solution 2 for WorkbookSource.plus_40002
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T05:15:44.153105+00:00
-- url     : https://prove2.me/submissions/79bef7bd-7990-464d-b889-18361f43cfba

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Real Nat

set_option maxHeartbeats 2000000 in
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + c * a) ≥ (a^2 + b * c - c * a) / (a^2 + a * b + b * c) + (b^2 + c * a - a * b) / (b^2 + b * c + c * a) + (c^2 + a * b - b * c) / (c^2 + c * a + a * b) := by
  rw [ge_iff_le, ← sub_nonneg]
  have key : ((a^2 + b^2 + c^2) / (a * b + b * c + c * a)) - ((a^2 + b * c - c * a) / (a^2 + a * b + b * c) + (b^2 + c * a - a * b) / (b^2 + b * c + c * a) + (c^2 + a * b - b * c) / (c^2 + c * a + a * b)) = (a^6*b*c + a^6*c^2 + 2*a^5*b^3 + 2*a^5*b^2*c - 2*a^5*b*c^2 - a^5*c^3 - a^4*b^4 - 3*a^4*b^3*c - 2*a^4*b^2*c^2 + a^4*b*c^3 - a^4*c^4 - a^3*b^5 + a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - 3*a^3*b*c^4 + 2*a^3*c^5 + a^2*b^6 - 2*a^2*b^5*c - 2*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 2*a^2*b^2*c^4 + 2*a^2*b*c^5 + a*b^6*c + 2*a*b^5*c^2 - 3*a*b^4*c^3 + a*b^3*c^4 - 2*a*b^2*c^5 + a*b*c^6 + 2*b^5*c^3 - b^4*c^4 - b^3*c^5 + b^2*c^6) / ((a^2 + a*b + b*c)*(a*b + a*c + c^2)*(a*b + a*c + b*c)*(a*c + b^2 + b*c)) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · have e : (a^6*b*c + a^6*c^2 + 2*a^5*b^3 + 2*a^5*b^2*c - 2*a^5*b*c^2 - a^5*c^3 - a^4*b^4 - 3*a^4*b^3*c - 2*a^4*b^2*c^2 + a^4*b*c^3 - a^4*c^4 - a^3*b^5 + a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - 3*a^3*b*c^4 + 2*a^3*c^5 + a^2*b^6 - 2*a^2*b^5*c - 2*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 2*a^2*b^2*c^4 + 2*a^2*b*c^5 + a*b^6*c + 2*a*b^5*c^2 - 3*a*b^4*c^3 + a*b^3*c^4 - 2*a*b^2*c^5 + a*b*c^6 + 2*b^5*c^3 - b^4*c^4 - b^3*c^5 + b^2*c^6) = (1070/5053) * (b^2*c^4) * (a + b - 2*c)^2 + (2441/10106) * (a^2*b*c^3) * (a + b - 2*c)^2 + (2085/5053) * (a^3*c^3) * (a + b - 2*c)^2 + (570/5053) * (a^4*b*c) * (a + b - 2*c)^2 + (2085/5053) * (b^3*c^3) * (a - 2*b + c)^2 + (570/5053) * (a*b*c^4) * (a - 2*b + c)^2 + (2441/10106) * (a*b^3*c^2) * (a - 2*b + c)^2 + (1070/5053) * (a^2*b^4) * (a - 2*b + c)^2 + (570/5053) * (a*b^4*c) * (-2*a + b + c)^2 + (2441/10106) * (a^3*b^2*c) * (-2*a + b + c)^2 + (2085/5053) * (a^3*b^3) * (-2*a + b + c)^2 + (1070/5053) * (a^4*c^2) * (-2*a + b + c)^2 + (1773/10106) * (a*b*c^2) * (a*b + b*c - 2*c^2)^2 + (61/5053) * (a^4) * (a*c + b^2 - 2*c^2)^2 + (107/5053) * (a^2*b*c) * (a^2 + a*b - 2*c^2)^2 + (712/5053) * (b^2*c^2) * (a*b - 2*b*c + c^2)^2 + (234/5053) * (b^3*c) * (a^2 - 2*b*c + c^2)^2 + (107/5053) * (a*b*c^2) * (a*c - 2*b^2 + c^2)^2 + (61/5053) * (c^4) * (a^2 - 2*b^2 + b*c)^2 + (1773/10106) * (a*b^2*c) * (a*b + a*c - 2*b^2)^2 + (712/5053) * (a^2*c^2) * (a^2 - 2*a*c + b*c)^2 + (234/5053) * (a*c^3) * (a^2 - 2*a*c + b^2)^2 + (234/5053) * (a^3*b) * (-2*a*b + b^2 + c^2)^2 + (712/5053) * (a^2*b^2) * (-2*a*b + a*c + b^2)^2 + (61/5053) * (b^4) * (-2*a^2 + a*b + c^2)^2 + (107/5053) * (a*b^2*c) * (-2*a^2 + b^2 + b*c)^2 + (1773/10106) * (a^2*b*c) * (-2*a^2 + a*c + b*c)^2 + (830/5053) * (a*b) * (a^2*b - 2*b^2*c + c^3)^2 + (830/5053) * (b*c) * (a^3 - 2*a*c^2 + b^2*c)^2 + (830/5053) * (a*c) * (-2*a^2*b + a*c^2 + b^3)^2 := by
      ring
    rw [e]
    positivity
  · positivity
