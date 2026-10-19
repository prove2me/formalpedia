-- Prove2me | solution 1 for actuarial_d_deferred_guarantee_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:08:04.24856+00:00
-- url     : https://prove2.me/submissions/400308fb-eabf-4864-a9c3-34693bbcbaee

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_deferGuaranteed
import Definitions.Def_actuarial_d_deferX
import Definitions.Def_actuarial_d_deferTopup

open ActuarialJointD

theorem solution (h a n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : deferGuaranteed h a n g p d b = deferX h a n p d b + deferTopup h a n g p d b := by
  simp only [ActuarialJointD.alive, ActuarialJointD.annRange, ActuarialJointD.deferGuaranteed, ActuarialJointD.deferTopup, ActuarialJointD.deferValue, ActuarialJointD.deferX, ActuarialJointD.expect, ActuarialJointD.guaranteeMember, ActuarialJointD.guaranteeTopup]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← mul_add, ← mul_sub]
  repeat refine Finset.sum_congr rfl fun _ _ => ?_
  try congr 1
  repeat refine Finset.sum_congr rfl fun _ _ => ?_
  beta_reduce
  split_ifs <;> ring
