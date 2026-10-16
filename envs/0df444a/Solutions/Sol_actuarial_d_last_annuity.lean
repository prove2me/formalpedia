-- Prove2me | solution 1 for actuarial_d_last_annuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T19:46:33.681833+00:00
-- url     : https://prove2.me/submissions/30bf7e3e-d101-4529-a1bc-c651a1a95ce6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_annPath
import Definitions.Def_actuarial_d_annValue
import Definitions.Def_actuarial_d_annX
import Definitions.Def_actuarial_d_annLast
import Definitions.Def_actuarial_d_annY
import Definitions.Def_actuarial_d_annJoint
import Definitions.Def_actuarial_d_annRev
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_both
import Definitions.Def_actuarial_d_last
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_px
import Definitions.Def_actuarial_d_py
import Definitions.Def_actuarial_d_plast
import Definitions.Def_actuarial_d_pxy
import Definitions.Def_actuarial_d_prev
import Definitions.Def_actuarial_cm1SingleLifeAnnuity
import Definitions.Def_actuarial_cm1JointLifeAnnuity
import Definitions.Def_actuarial_cm1LastSurvivorAnnuity
import Theorems.Thm_actuarial_d_last_inclusion
import Theorems.Thm_ActuarialValuation_cm1LastSurvivorAnnuity_decompose

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

private theorem annValue_fubini (h n : ℕ) (p : ℕ → ℕ → ℝ)
    (d b : ℕ → ℝ) (s : ℕ → ℕ → ℕ → ℝ) :
    annValue h n p d b s =
      ∑ t ∈ Finset.range n, (d t * b t) * expect h p (fun i j => s i j t) := by
  unfold annValue annPath expect
  calc
    (∑ i ∈ Finset.range (h+1), ∑ j ∈ Finset.range (h+1),
        p i j * (∑ t ∈ Finset.range n, d t * b t * s i j t)) =
      ∑ i ∈ Finset.range (h+1), ∑ j ∈ Finset.range (h+1),
        ∑ t ∈ Finset.range n, p i j * (d t * b t * s i j t) := by
          simp_rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range (h+1), ∑ t ∈ Finset.range n,
          ∑ j ∈ Finset.range (h+1), p i j * (d t * b t * s i j t) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
    _ = ∑ t ∈ Finset.range n, ∑ i ∈ Finset.range (h+1),
          ∑ j ∈ Finset.range (h+1), p i j * (d t * b t * s i j t) := by
          rw [Finset.sum_comm]
    _ = ∑ t ∈ Finset.range n, (d t * b t) *
          (∑ i ∈ Finset.range (h+1), ∑ j ∈ Finset.range (h+1),
             p i j * s i j t) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring

theorem solution (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) :
    annLast h n p d b = annX h n p d b + annY h n p d b - annJoint h n p d b := by
  let w : ℕ → ℝ := fun t => d t * b t
  have hP (t : ℕ) : plast h p t = px h p t + py h p t - pxy h p t := by
    unfold plast px py pxy expect
    simp_rw [actuarial_d_last_inclusion]
    simp_rw [mul_sub, mul_add]
    simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hX : annX h n p d b =
      ActuarialValuation.cm1SingleLifeAnnuity w (px h p) n := by
    unfold annX
    rw [annValue_fubini]
    rfl
  have hY : annY h n p d b =
      ActuarialValuation.cm1SingleLifeAnnuity w (py h p) n := by
    unfold annY
    rw [annValue_fubini]
    rfl
  have hJoint : annJoint h n p d b =
      ActuarialValuation.cm1JointLifeAnnuity w (pxy h p) n := by
    unfold annJoint
    rw [annValue_fubini]
    rfl
  have hLast : annLast h n p d b =
      ActuarialValuation.cm1LastSurvivorAnnuity w (px h p) (py h p) (pxy h p) n := by
    unfold annLast
    rw [annValue_fubini]
    unfold ActuarialValuation.cm1LastSurvivorAnnuity
    apply Finset.sum_congr rfl
    intro t ht
    change (d t * b t) * plast h p t =
      (d t * b t) * (px h p t + py h p t - pxy h p t)
    rw [hP t]
  rw [hLast, hX, hY, hJoint]
  have hxlv := ActuarialValuation.cm1LastSurvivorAnnuity_decompose
    w (px h p) (py h p) (pxy h p) n
  linear_combination hxlv
