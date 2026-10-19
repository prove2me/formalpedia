-- Prove2me | solution 1 for actuarial_d_guarantee_topup_occupation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T11:53:26.129154+00:00
-- url     : https://prove2.me/submissions/1a641801-954d-4146-a389-9b19aae3fe21

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_guaranteeMember
import Definitions.Def_actuarial_d_guaranteeTopup
import Definitions.Def_actuarial_d_alive

open ActuarialJointD

theorem solution (g i t : ℕ) : guaranteeMember g i t = alive i t + guaranteeTopup g i t := by
  simp only [ActuarialJointD.alive, ActuarialJointD.guaranteeMember, ActuarialJointD.guaranteeTopup]; split_ifs <;> simp_all <;> linarith
