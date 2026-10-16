-- Prove2me | solution 1 for actuarial_d_member_spouse_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T19:49:34.960539+00:00
-- url     : https://prove2.me/submissions/1051c7de-ab7c-4529-843d-7eec3856878b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_d_annMemberSpouse
import Definitions.Def_actuarial_d_annLast
import Definitions.Def_actuarial_d_annValue
import Definitions.Def_actuarial_d_annPath
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_last
import Theorems.Thm_actuarial_d_reversion_complement
import Theorems.Thm_actuarial_d_last_inclusion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) :
    annMemberSpouse h n p d b 1 = annLast h n p d b := by
  have hstate (i j t : ℕ) : alive i t + onlyY i j t = last i j t := by
    rw [actuarial_d_reversion_complement, actuarial_d_last_inclusion]
    ring
  unfold annMemberSpouse annLast annValue annPath expect
  simp_rw [one_mul, hstate]
