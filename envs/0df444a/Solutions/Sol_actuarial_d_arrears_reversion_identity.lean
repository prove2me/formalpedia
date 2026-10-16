-- Prove2me | solution 1 for actuarial_d_arrears_reversion_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T04:58:46.76299+00:00
-- url     : https://prove2.me/submissions/24a50849-a067-4286-af7b-e743702c5b92

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_arrearsRev
import Definitions.Def_actuarial_d_arrearsY
import Definitions.Def_actuarial_d_arrearsJoint
import Definitions.Def_actuarial_d_arrearsValue
import Definitions.Def_actuarial_d_arrearsPath
import Definitions.Def_actuarial_d_expect
import Theorems.Thm_actuarial_d_reversion_complement
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) :
    arrearsRev h n p d b = arrearsY h n p d b - arrearsJoint h n p d b := by
  unfold arrearsRev arrearsY arrearsJoint arrearsValue arrearsPath expect
  simp_rw [actuarial_d_reversion_complement]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] <;> ring
