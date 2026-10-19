-- Prove2me | solution 1 for actuarial_d_guarantee_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T11:52:40.780836+00:00
-- url     : https://prove2.me/submissions/39c8d269-d90a-48ba-b937-fc50aee09355

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_guaranteeMember
import Definitions.Def_actuarial_d_alive

open ActuarialJointD

theorem solution (i t : ℕ) : guaranteeMember 0 i t = alive i t := by
  simp [ActuarialJointD.alive, ActuarialJointD.guaranteeMember]
