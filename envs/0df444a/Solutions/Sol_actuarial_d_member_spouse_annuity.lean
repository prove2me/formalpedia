-- Prove2me | solution 1 for actuarial_d_member_spouse_annuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T19:57:58.160795+00:00
-- url     : https://prove2.me/submissions/33db4e8a-023c-44d8-a9e6-ec2b53ecc51c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_d_annMemberSpouse
import Definitions.Def_actuarial_d_annX
import Definitions.Def_actuarial_d_annRev
import Definitions.Def_actuarial_d_annValue
import Definitions.Def_actuarial_d_annPath
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_onlyY

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

private theorem annPath_member_spouse_split (n : ℕ) (d b : ℕ → ℝ)
    (rho : ℝ) (i j : ℕ) :
    annPath n d b (fun t => alive i t + rho * onlyY i j t) =
    annPath n d b (alive i) + rho * annPath n d b (onlyY i j) := by
  unfold annPath
  calc
    (∑ t ∈ Finset.range n, d t * b t * (alive i t + rho * onlyY i j t)) =
       ∑ t ∈ Finset.range n,
         (d t * b t * alive i t + rho * (d t * b t * onlyY i j t)) := by
           apply Finset.sum_congr rfl
           intro t ht
           ring
    _ = (∑ t ∈ Finset.range n, d t * b t * alive i t) +
         rho * (∑ t ∈ Finset.range n, d t * b t * onlyY i j t) := by
           simp only [Finset.sum_add_distrib, Finset.mul_sum]

private theorem expect_scaled_add (h : ℕ) (p : ℕ → ℕ → ℝ)
    (rho : ℝ) (u v : ℕ → ℕ → ℝ) :
    expect h p (fun i j => u i j + rho * v i j) =
      expect h p u + rho * expect h p v := by
  unfold expect
  calc
    (∑ i ∈ Finset.range (h+1), ∑ j ∈ Finset.range (h+1),
       p i j * (u i j + rho * v i j)) =
       ∑ i ∈ Finset.range (h+1), ∑ j ∈ Finset.range (h+1),
       (p i j * u i j + rho * (p i j * v i j)) := by
         apply Finset.sum_congr rfl
         intro i hi
         apply Finset.sum_congr rfl
         intro j hj
         ring
    _ = (∑ i ∈ Finset.range (h+1), ∑ j ∈ Finset.range (h+1),
           p i j * u i j) +
         rho * (∑ i ∈ Finset.range (h+1), ∑ j ∈ Finset.range (h+1),
           p i j * v i j) := by
           simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem solution (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho : ℝ) :
    annMemberSpouse h n p d b rho = annX h n p d b + rho * annRev h n p d b := by
  unfold annMemberSpouse annX annRev annValue
  simp_rw [annPath_member_spouse_split]
  exact expect_scaled_add h p rho
    (fun i j => annPath n d b (alive i))
    (fun i j => annPath n d b (onlyY i j))
