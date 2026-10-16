-- Prove2me | solution 1 for actuarial_d_defer_reversion_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T20:24:17.418183+00:00
-- url     : https://prove2.me/submissions/7ea0cee1-2b7d-475f-8f14-4fee04414585

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_deferRev
import Definitions.Def_actuarial_d_deferY
import Definitions.Def_actuarial_d_deferJoint
import Definitions.Def_actuarial_d_deferValue
import Definitions.Def_actuarial_d_annRange
import Definitions.Def_actuarial_d_expect
import Theorems.Thm_actuarial_d_reversion_complement
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h a n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) :
    deferRev h a n p d b = deferY h a n p d b - deferJoint h a n p d b := by
  unfold deferRev deferY deferJoint deferValue annRange expect
  simp_rw [actuarial_d_reversion_complement]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] <;> ring
