-- Prove2me | solution 1 for actuarial_d_first_assurance_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T19:46:43.959351+00:00
-- url     : https://prove2.me/submissions/706870c6-bd29-4c35-be21-323317a5e22f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_assureFirst
import Definitions.Def_actuarial_d_assureXFirst
import Definitions.Def_actuarial_d_assureYFirst
import Definitions.Def_actuarial_d_assureTie
import Theorems.Thm_actuarial_d_first_order_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) :
    assureFirst h p d = assureXFirst h p d + assureYFirst h p d + assureTie h p d := by
  unfold assureFirst assureXFirst assureYFirst assureTie expect
  simp_rw [actuarial_d_first_order_partition]
  simp_rw [mul_add]
  simp_rw [Finset.sum_add_distrib]
