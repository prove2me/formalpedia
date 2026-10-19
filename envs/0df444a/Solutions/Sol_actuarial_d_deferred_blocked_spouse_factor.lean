-- Prove2me | solution 1 for actuarial_d_deferred_blocked_spouse_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:07:22.227302+00:00
-- url     : https://prove2.me/submissions/6057548a-267a-4a10-b1fa-993a0be322e2

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_deferBlockedRev
import Definitions.Def_actuarial_d_deferRev
import Definitions.Def_actuarial_d_deferOverlap

open ActuarialJointD

theorem solution (h a n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : deferBlockedRev h a n g p d b = deferRev h a n p d b - deferOverlap h a n g p d b := by
  simp only [ActuarialJointD.alive, ActuarialJointD.annRange, ActuarialJointD.dead, ActuarialJointD.deferBlockedRev, ActuarialJointD.deferOverlap, ActuarialJointD.deferRev, ActuarialJointD.deferValue, ActuarialJointD.delayedSpouse, ActuarialJointD.expect, ActuarialJointD.onlyY]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← mul_add, ← mul_sub]
  repeat refine Finset.sum_congr rfl fun _ _ => ?_
  try congr 1
  repeat refine Finset.sum_congr rfl fun _ _ => ?_
  beta_reduce
  split_ifs <;> ring
