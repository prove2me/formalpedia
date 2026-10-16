-- Prove2me | solution 1 for actuarial_d_member_spouse_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T20:03:08.75551+00:00
-- url     : https://prove2.me/submissions/210ac0b2-dc03-4faa-8818-fc9448e2faaf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_d_annMemberSpouse
import Definitions.Def_actuarial_d_annX
import Definitions.Def_actuarial_d_annY
import Definitions.Def_actuarial_d_annJoint
import Definitions.Def_actuarial_d_annRev
import Definitions.Def_actuarial_d_annLast
import Theorems.Thm_actuarial_d_member_spouse_annuity
import Theorems.Thm_actuarial_d_reversionary_annuity
import Theorems.Thm_actuarial_d_last_annuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho : ℝ) :
    annMemberSpouse h n p d b rho =
      (1-rho) * annX h n p d b + rho * annLast h n p d b := by
  rw [actuarial_d_member_spouse_annuity,
      actuarial_d_reversionary_annuity,
      actuarial_d_last_annuity]
  ring
