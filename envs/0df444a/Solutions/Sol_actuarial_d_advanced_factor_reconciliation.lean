-- Prove2me | solution 1 for actuarial_d_advanced_factor_reconciliation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T15:22:16.273704+00:00
-- url     : https://prove2.me/submissions/c47a9866-b12d-4f96-95df-b250a1ef5c28

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_advancedValue
import Definitions.Def_actuarial_d_deferX
import Definitions.Def_actuarial_d_deferTopup
import Definitions.Def_actuarial_d_deferY
import Definitions.Def_actuarial_d_deferJoint
import Definitions.Def_actuarial_d_deferOverlap
import Definitions.Def_actuarial_d_assureFirst
import Definitions.Def_actuarial_d_assureSecond
import Definitions.Def_actuarial_d_assureXFirst
import Definitions.Def_actuarial_d_assureYFirst
import Definitions.Def_actuarial_d_assureTie
import Definitions.Def_actuarial_d_advancedPath
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_annRange
import Definitions.Def_actuarial_d_deferValue
import Definitions.Def_actuarial_d_guaranteeMember
import Definitions.Def_actuarial_d_guaranteeTopup
import Definitions.Def_actuarial_d_delayedSpouse
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_both
import Definitions.Def_actuarial_d_dead
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h a n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho f s fx fy ft : ℝ) : advancedValue h a n g p d b rho f s fx fy ft = deferX h a n p d b + deferTopup h a n g p d b + rho * (deferY h a n p d b - deferJoint h a n p d b - deferOverlap h a n g p d b) + f * assureFirst h p d + s * assureSecond h p d + fx * assureXFirst h p d + fy * assureYFirst h p d + ft * assureTie h p d := by
  classical
  have hannAdd (F G : ℕ → ℝ) :
      annRange a n d b (fun t => F t + G t) =
      annRange a n d b F + annRange a n d b G := by
    unfold annRange
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hannSub (F G : ℕ → ℝ) :
      annRange a n d b (fun t => F t - G t) =
      annRange a n d b F - annRange a n d b G := by
    unfold annRange
    rw [← Finset.sum_sub_distrib]
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
  have hexpSub (F G : ℕ → ℕ → ℝ) :
      expect h p (fun i j => F i j - G i j) =
      expect h p F - expect h p G := by
    unfold expect
    simp only [mul_sub, Finset.sum_sub_distrib]
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
  have hpay (i j t : ℕ) :
      guaranteeMember g i t + rho * delayedSpouse g i j t =
      alive i t + guaranteeTopup g i t +
        rho * (alive j t - both i j t -
          (if t < g then onlyY i j t else 0)) := by
    by_cases ht : t < g
    · simp [guaranteeMember, guaranteeTopup, delayedSpouse,
        onlyY, both, dead, ht] <;> (try ring) <;> simp
    · simp [guaranteeMember, guaranteeTopup, delayedSpouse,
        onlyY, both, dead, ht] <;> (try ring) <;> simp
  have hpath (i j : ℕ) :
      advancedPath h a n g d b rho f s fx fy ft i j =
      annRange a n d b (fun t => alive i t) +
      annRange a n d b (fun t => guaranteeTopup g i t) +
      rho * (annRange a n d b (fun t => alive j t) -
        annRange a n d b (fun t => both i j t) -
        annRange a n d b
          (fun t => if t < g then onlyY i j t else 0)) +
      f * firstPath h d i j + s * secondPath h d i j +
      fx * xFirstPath h d i j + fy * yFirstPath h d i j +
      ft * tiePath h d i j := by
    have hc :
        (fun t => guaranteeMember g i t +
          rho * delayedSpouse g i j t) =
        (fun t => alive i t + guaranteeTopup g i t +
          rho * (alive j t - both i j t -
            (if t < g then onlyY i j t else 0))) := by
      funext t
      exact hpay i j t
    unfold advancedPath
    rw [hc]
    simp only [hannAdd, hannMul, hannSub]
  unfold advancedValue deferX deferTopup deferY deferJoint deferOverlap
    deferValue assureFirst assureSecond assureXFirst assureYFirst assureTie
  simp_rw [hpath]
  simp only [hexpAdd, hexpMul, hexpSub]
