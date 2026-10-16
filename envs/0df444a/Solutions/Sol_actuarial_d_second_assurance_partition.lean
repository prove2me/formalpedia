-- Prove2me | solution 1 for actuarial_d_second_assurance_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T19:46:57.291797+00:00
-- url     : https://prove2.me/submissions/a745823e-7a44-4f39-a482-474a2be9b984

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_assureSecond
import Definitions.Def_actuarial_d_assureXSecond
import Definitions.Def_actuarial_d_assureYSecond
import Definitions.Def_actuarial_d_assureTie
import Theorems.Thm_actuarial_d_second_order_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) :
    assureSecond h p d = assureXSecond h p d + assureYSecond h p d + assureTie h p d := by
  unfold assureSecond assureXSecond assureYSecond assureTie expect
  simp_rw [actuarial_d_second_order_partition]
  simp_rw [mul_add]
  simp_rw [Finset.sum_add_distrib]
