-- Prove2me | solution 1 for actuarial_d_guarantee_free_value
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T11:51:12.690449+00:00
-- url     : https://prove2.me/submissions/b0d67bb6-c3bf-4e0f-b34b-362d7e665ba1

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_guaranteeDelayValue
import Definitions.Def_actuarial_d_annMemberSpouse

open ActuarialJointD

theorem solution (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho : ℝ) : guaranteeDelayValue h n 0 p d b rho = annMemberSpouse h n p d b rho := by
  simp [ActuarialJointD.alive, ActuarialJointD.annMemberSpouse, ActuarialJointD.annPath, ActuarialJointD.annValue, ActuarialJointD.dead, ActuarialJointD.delayedSpouse, ActuarialJointD.expect, ActuarialJointD.guaranteeDelayPath, ActuarialJointD.guaranteeDelayValue, ActuarialJointD.guaranteeMember, ActuarialJointD.onlyY]
