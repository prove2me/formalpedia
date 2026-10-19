-- Prove2me | solution 1 for actuarial_d_capstone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T15:16:19.57423+00:00
-- url     : https://prove2.me/submissions/8b695517-3ab7-4e0c-b461-d285b63d6d1f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_totalValue
import Definitions.Def_actuarial_d_totalPath
import Definitions.Def_actuarial_d_annX
import Definitions.Def_actuarial_d_annRev
import Definitions.Def_actuarial_d_annLast
import Definitions.Def_actuarial_d_assureFirst
import Definitions.Def_actuarial_d_assureSecond
import Definitions.Def_actuarial_d_assureXFirst
import Definitions.Def_actuarial_d_assureYFirst
import Definitions.Def_actuarial_d_assureTie
import Definitions.Def_actuarial_d_assureXSecond
import Definitions.Def_actuarial_d_assureYSecond
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_annValue
import Definitions.Def_actuarial_d_annPath
import Definitions.Def_actuarial_d_annMemberSpouse
import Theorems.Thm_actuarial_d_member_spouse_annuity
import Theorems.Thm_actuarial_d_member_spouse_last
import Theorems.Thm_actuarial_d_first_assurance_partition
import Theorems.Thm_actuarial_d_second_assurance_partition
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho f s fx fy ft : ℝ) : totalValue h n p d b rho f s fx fy ft = annX h n p d b + rho * annRev h n p d b + f * assureFirst h p d + s * assureSecond h p d + fx * assureXFirst h p d + fy * assureYFirst h p d + ft * assureTie h p d ∧ totalValue h n p d b rho f s fx fy ft = (1-rho) * annX h n p d b + rho * annLast h n p d b + f * assureFirst h p d + s * assureSecond h p d + fx * assureXFirst h p d + fy * assureYFirst h p d + ft * assureTie h p d ∧ assureFirst h p d = assureXFirst h p d + assureYFirst h p d + assureTie h p d ∧ assureSecond h p d = assureXSecond h p d + assureYSecond h p d + assureTie h p d := by
  classical
  have hexpAdd (F G : ℕ → ℕ → ℝ) :
      expect h p (fun i j => F i j + G i j) =
      expect h p F + expect h p G := by
    unfold expect
    simp only [mul_add, Finset.sum_add_distrib]
  have hexpMul (r : ℝ) (F : ℕ → ℕ → ℝ) :
      expect h p (fun i j => r * F i j) =
      r * expect h p F := by
    unfold expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hcore :
      totalValue h n p d b rho f s fx fy ft =
      annMemberSpouse h n p d b rho +
      f * assureFirst h p d + s * assureSecond h p d +
      fx * assureXFirst h p d + fy * assureYFirst h p d +
      ft * assureTie h p d := by
    unfold totalValue annMemberSpouse annValue
      assureFirst assureSecond assureXFirst assureYFirst assureTie
    simp_rw [totalPath]
    simp only [hexpAdd, hexpMul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcore, actuarial_d_member_spouse_annuity]
  · rw [hcore, actuarial_d_member_spouse_last]
  · exact actuarial_d_first_assurance_partition h p d
  · exact actuarial_d_second_assurance_partition h p d
