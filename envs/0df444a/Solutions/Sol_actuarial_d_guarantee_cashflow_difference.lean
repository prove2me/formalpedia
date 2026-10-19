-- Prove2me | solution 1 for actuarial_d_guarantee_cashflow_difference
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:08:42.365608+00:00
-- url     : https://prove2.me/submissions/3602a833-10b3-4bd4-98c2-dc979e2ecc4f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_guaranteeParallelPath
import Definitions.Def_actuarial_d_guaranteeDelayPath
import Definitions.Def_actuarial_d_guaranteeOverlapPath

open ActuarialJointD

theorem solution (n g i j : ℕ) (d b : ℕ → ℝ) (rho : ℝ) : guaranteeParallelPath n g d b rho i j = guaranteeDelayPath n g d b rho i j + rho * guaranteeOverlapPath n g d b i j := by
  simp only [ActuarialJointD.alive, ActuarialJointD.annPath, ActuarialJointD.dead, ActuarialJointD.delayedSpouse, ActuarialJointD.guaranteeDelayPath, ActuarialJointD.guaranteeMember, ActuarialJointD.guaranteeOverlapPath, ActuarialJointD.guaranteeParallelPath, ActuarialJointD.onlyY]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← mul_add, ← mul_sub]
  repeat refine Finset.sum_congr rfl fun _ _ => ?_
  try congr 1
  repeat refine Finset.sum_congr rfl fun _ _ => ?_
  beta_reduce
  split_ifs <;> ring
