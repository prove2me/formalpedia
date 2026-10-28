-- Prove2me | solution 1 for actuarial_f_member_before_retirement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:32:23.650806+00:00
-- url     : https://prove2.me/submissions/b62bb74a-02c2-4c52-9d6a-2d52680630f1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue

open ActuarialUnderpinsF

theorem solution (r i t : ℕ) (ht : t < r) :
    memberDue r i t = 0 := by
  unfold memberDue
  rw [if_neg (by omega)]
