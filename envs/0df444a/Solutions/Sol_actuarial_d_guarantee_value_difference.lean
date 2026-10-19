-- Prove2me | solution 1 for actuarial_d_guarantee_value_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T15:13:28.058989+00:00
-- url     : https://prove2.me/submissions/123722ba-71ca-4706-8dc3-e4eaf33430c2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_guaranteeParallelValue
import Definitions.Def_actuarial_d_guaranteeDelayValue
import Definitions.Def_actuarial_d_guaranteeOverlapValue
import Definitions.Def_actuarial_d_guaranteeParallelPath
import Definitions.Def_actuarial_d_guaranteeDelayPath
import Definitions.Def_actuarial_d_guaranteeOverlapPath
import Definitions.Def_actuarial_d_guaranteeMember
import Definitions.Def_actuarial_d_delayedSpouse
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_annPath
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho : ℝ) : guaranteeParallelValue h n g p d b rho = guaranteeDelayValue h n g p d b rho + rho * guaranteeOverlapValue h n g p d b := by
  classical
  have hpath (i j : ℕ) :
      guaranteeParallelPath n g d b rho i j =
      guaranteeDelayPath n g d b rho i j +
        rho * guaranteeOverlapPath n g d b i j := by
    unfold guaranteeParallelPath guaranteeDelayPath guaranteeOverlapPath annPath
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases htg : t < g
    · simp [delayedSpouse, htg]
      try ring
    · simp [delayedSpouse, htg]
      try ring
  have hadd (F G : ℕ → ℕ → ℝ) :
      expect h p (fun i j => F i j + G i j) =
      expect h p F + expect h p G := by
    unfold expect
    simp only [mul_add, Finset.sum_add_distrib]
  have hscale (F : ℕ → ℕ → ℝ) :
      expect h p (fun i j => rho * F i j) =
      rho * expect h p F := by
    unfold expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  change expect h p (fun i j => guaranteeParallelPath n g d b rho i j) =
      expect h p (fun i j => guaranteeDelayPath n g d b rho i j) +
      rho * expect h p (fun i j => guaranteeOverlapPath n g d b i j)
  calc
    _ = expect h p (fun i j =>
          guaranteeDelayPath n g d b rho i j +
          rho * guaranteeOverlapPath n g d b i j) := by
        unfold expect
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simpa only using congrArg
          (fun v : ℝ => p i j * v) (hpath i j)
    _ = expect h p (fun i j => guaranteeDelayPath n g d b rho i j) +
        rho * expect h p (fun i j => guaranteeOverlapPath n g d b i j) := by
        rw [hadd, hscale]
