-- Prove2me | solution 1 for actuarial_f_member_due_at_retirement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:32:42.784948+00:00
-- url     : https://prove2.me/submissions/fa411a93-4fb8-48e8-bb02-c8f0e2604d55

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue

open ActuarialUnderpinsF

theorem solution (r i : ℕ) (hr : r ≤ i) :
    memberDue r i r = 1 := by
  unfold memberDue ActuarialJointD.alive
  rw [if_pos le_rfl, if_pos hr]
