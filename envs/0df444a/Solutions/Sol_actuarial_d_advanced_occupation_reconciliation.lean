-- Prove2me | solution 1 for actuarial_d_advanced_occupation_reconciliation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T15:11:27.900408+00:00
-- url     : https://prove2.me/submissions/8a57a60c-0a3b-4f72-9eb6-960eb1122704

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_advancedValue
import Definitions.Def_actuarial_d_deferGuaranteed
import Definitions.Def_actuarial_d_deferBlockedRev
import Definitions.Def_actuarial_d_assureFirst
import Definitions.Def_actuarial_d_assureSecond
import Definitions.Def_actuarial_d_assureXFirst
import Definitions.Def_actuarial_d_assureYFirst
import Definitions.Def_actuarial_d_assureTie
import Definitions.Def_actuarial_d_advancedPath
import Definitions.Def_actuarial_d_deferValue
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_annRange
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h a n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho f s fx fy ft : ℝ) : advancedValue h a n g p d b rho f s fx fy ft = deferGuaranteed h a n g p d b + rho * deferBlockedRev h a n g p d b + f * assureFirst h p d + s * assureSecond h p d + fx * assureXFirst h p d + fy * assureYFirst h p d + ft * assureTie h p d := by
  classical
  have hannAdd (F G : ℕ → ℝ) :
      annRange a n d b (fun t => F t + G t) =
      annRange a n d b F + annRange a n d b G := by
    unfold annRange
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hannMul (r : ℝ) (F : ℕ → ℝ) :
      annRange a n d b (fun t => r * F t) =
      r * annRange a n d b F := by
    unfold annRange
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
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
  have hpath (i j : ℕ) :
      advancedPath h a n g d b rho f s fx fy ft i j =
      annRange a n d b (fun t => guaranteeMember g i t) +
        rho * annRange a n d b (fun t => delayedSpouse g i j t) +
        f * firstPath h d i j + s * secondPath h d i j +
        fx * xFirstPath h d i j + fy * yFirstPath h d i j +
        ft * tiePath h d i j := by
    unfold advancedPath
    rw [hannAdd, hannMul]
  unfold advancedValue deferGuaranteed deferBlockedRev deferValue
    assureFirst assureSecond assureXFirst assureYFirst assureTie
  simp_rw [hpath]
  simp only [hexpAdd, hexpMul]
