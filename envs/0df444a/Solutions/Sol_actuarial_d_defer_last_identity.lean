-- Prove2me | solution 1 for actuarial_d_defer_last_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T20:24:15.822785+00:00
-- url     : https://prove2.me/submissions/6b41eace-1be3-428a-b91b-36b11faa70f4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_deferLast
import Definitions.Def_actuarial_d_deferX
import Definitions.Def_actuarial_d_deferY
import Definitions.Def_actuarial_d_deferJoint
import Definitions.Def_actuarial_d_deferValue
import Definitions.Def_actuarial_d_annRange
import Definitions.Def_actuarial_d_expect
import Theorems.Thm_actuarial_d_last_inclusion
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h a n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) :
    deferLast h a n p d b = deferX h a n p d b + deferY h a n p d b - deferJoint h a n p d b := by
  unfold deferLast deferX deferY deferJoint deferValue annRange expect
  simp_rw [actuarial_d_last_inclusion]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] <;> ring
