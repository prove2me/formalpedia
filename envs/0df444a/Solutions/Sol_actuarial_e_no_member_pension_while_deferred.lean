-- Prove2me | solution 1 for actuarial_e_no_member_pension_while_deferred
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:41:56.361849+00:00
-- url     : https://prove2.me/submissions/26a3427e-ae95-48c1-937d-5e5f458495ac

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_memberPayment

open ActuarialDeathE

theorem solution (r i t : ℕ) (base : ℕ → ℝ) (hi : i < r) : memberPayment r i t base = 0 := by
  unfold memberPayment alive ActuarialJointD.alive
  split_ifs <;> first | omega | simp
