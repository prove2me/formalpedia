-- Prove2me | solution 1 for actuarial_d_arrears_last_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T04:58:27.253783+00:00
-- url     : https://prove2.me/submissions/4cac2946-0346-4e8b-a2d6-73c6511b1136

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_arrearsLast
import Definitions.Def_actuarial_d_arrearsX
import Definitions.Def_actuarial_d_arrearsY
import Definitions.Def_actuarial_d_arrearsJoint
import Definitions.Def_actuarial_d_arrearsValue
import Definitions.Def_actuarial_d_arrearsPath
import Definitions.Def_actuarial_d_expect
import Theorems.Thm_actuarial_d_last_inclusion
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) :
    arrearsLast h n p d b = arrearsX h n p d b + arrearsY h n p d b - arrearsJoint h n p d b := by
  unfold arrearsLast arrearsX arrearsY arrearsJoint arrearsValue arrearsPath expect
  simp_rw [actuarial_d_last_inclusion]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] <;> ring
