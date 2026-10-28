-- Prove2me | solution 1 for actuarial_f_member_after_terminal_year
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:32:34.425649+00:00
-- url     : https://prove2.me/submissions/b02c16b2-445a-47cf-a7d6-1ff55a1a5063

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue

open ActuarialUnderpinsF

theorem solution (r i t : ℕ) (hi : i < t) :
    memberDue r i t = 0 := by
  unfold memberDue ActuarialJointD.alive
  split_ifs <;> first | rfl | omega
