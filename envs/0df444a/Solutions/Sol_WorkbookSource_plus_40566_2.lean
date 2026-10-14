-- Prove2me | solution 2 for WorkbookSource.plus_40566
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T05:14:37.036215+00:00
-- url     : https://prove2.me/submissions/90cedf08-cb05-45b3-b719-3ad6f40edd93

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Real Nat

set_option maxHeartbeats 2000000 in
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 6) : a / (b ^ 2 + c + 1) + b / (c ^ 2 + a + 1) + c / (a ^ 2 + b + 1) ≥ 6 / 7 := by
  rw [ge_iff_le, ← sub_nonneg]
  have key : (a / (b ^ 2 + c + 1) + b / (c ^ 2 + a + 1) + c / (a ^ 2 + b + 1)) - (6 / 7) = (7*a^4 - 6*a^3*b^2 + 7*a^3*c^2 - 6*a^3*c + a^3 + 7*a^2*b^3 - 6*a^2*b^2*c^2 - 6*a^2*b^2 + 7*a^2*b*c + 14*a^2*b - 6*a^2*c^3 - 6*a^2*c^2 - 6*a^2*c + a^2 - 6*a*b^3 + 7*a*b^2*c - 6*a*b^2 + 7*a*b*c^2 - 6*a*b*c + a*b + 14*a*c^2 + a*c + a + 7*b^4 - 6*b^3*c^2 + b^3 + 7*b^2*c^3 - 6*b^2*c^2 + 14*b^2*c + b^2 - 6*b*c^3 - 6*b*c^2 + b*c + b + 7*c^4 + c^3 + c^2 + c - 6) / (7*(a + c^2 + 1)*(a^2 + b + 1)*(b^2 + c + 1)) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · have e : (7*a^4 - 6*a^3*b^2 + 7*a^3*c^2 - 6*a^3*c + a^3 + 7*a^2*b^3 - 6*a^2*b^2*c^2 - 6*a^2*b^2 + 7*a^2*b*c + 14*a^2*b - 6*a^2*c^3 - 6*a^2*c^2 - 6*a^2*c + a^2 - 6*a*b^3 + 7*a*b^2*c - 6*a*b^2 + 7*a*b*c^2 - 6*a*b*c + a*b + 14*a*c^2 + a*c + a + 7*b^4 - 6*b^3*c^2 + b^3 + 7*b^2*c^3 - 6*b^2*c^2 + 14*b^2*c + b^2 - 6*b*c^3 - 6*b*c^2 + b*c + b + 7*c^4 + c^3 + c^2 + c - 6) = (7/27) * (b^3*c) * (-b + c)^2 + (7/288) * (a*c^3) * (-b + c)^2 + (883/2592) * (a*b^2*c) * (-b + c)^2 + (251/324) * (a^2*b*c) * (-b + c)^2 + (203/864) * (a*c^3) * (-a + c)^2 + (121/288) * (a*b*c^2) * (-a + c)^2 + (377/432) * (a*b^2*c) * (-a + c)^2 + (37/864) * (a^3*b) * (-a + c)^2 + (251/324) * (a*b*c^2) * (-a + b)^2 + (25/54) * (a^2*b*c) * (-a + b)^2 + (187/864) * (a^3*b) * (-a + b)^2 + (275/1296) * (b*c) * (-b^2 + c^2)^2 + (235/1296) * (b^2) * (-b^2 + c^2)^2 + (989/2592) * (b^2) * (-a*b + c^2)^2 + (5/864) * (a*b) * (-a*b + c^2)^2 + (203/1296) * (c^2) * (-a^2 + c^2)^2 + (275/1296) * (a*c) * (-a^2 + c^2)^2 + (29/96) * (c^2) * (-a^2 + b*c)^2 + (95/2592) * (a*c) * (-a*c + b^2)^2 + (799/2592) * (a^2) * (-a*c + b^2)^2 + (127/1296) * (c^2) * (-a^2 + b^2)^2 + (275/1296) * (a*b) * (-a^2 + b^2)^2 + (227/1296) * (a^2) * (-a^2 + b^2)^2 + (1/54) * (1) * (-b^3 + c^3)^2 + (2/81) * (1) * (-a^3 + c^3)^2 := by
      have hc' : c = 6 - a - b := by linarith
      subst hc'
      ring
    rw [e]
    positivity
  · positivity
