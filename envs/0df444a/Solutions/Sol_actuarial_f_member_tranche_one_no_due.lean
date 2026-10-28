-- Prove2me | solution 1 for actuarial_f_member_tranche_one_no_due
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:39:37.930771+00:00
-- url     : https://prove2.me/submissions/b8cbbb59-8615-4d14-957f-e9b686524967

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberTrancheOne

open ActuarialUnderpinsF

theorem solution (r z i t : ℕ)
    (a b g0 : ℕ → ℝ) (ht : i < t) :
    memberTrancheOne r z i t a b g0 = 0 := by
  have hm : memberDue r i t = 0 := by
    unfold memberDue ActuarialJointD.alive
    split_ifs <;> first | rfl | omega
  unfold memberTrancheOne
  rw [hm, mul_zero]
