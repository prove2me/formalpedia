-- Prove2me | solution 1 for actuarial_d_defer_member_spouse_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T20:25:11.389086+00:00
-- url     : https://prove2.me/submissions/d4a42733-1a50-47bb-a821-9dfee42d3215

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_d_deferMemberSpouse
import Definitions.Def_actuarial_d_deferX
import Definitions.Def_actuarial_d_deferRev
import Definitions.Def_actuarial_d_deferValue
import Definitions.Def_actuarial_d_annRange
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_onlyY

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

private theorem annRange_member_spouse_split (a n : ℕ) (d b : ℕ → ℝ)
    (rho : ℝ) (i j : ℕ) :
    annRange a n d b (fun t => alive i t + rho * onlyY i j t) =
    annRange a n d b (alive i) + rho * annRange a n d b (onlyY i j) := by
  unfold annRange
  calc
    (∑ t ∈ Finset.range n, d (a+t) * b (a+t) * (alive i (a+t) + rho * onlyY i j (a+t))) =
       ∑ t ∈ Finset.range n,
         (d (a+t) * b (a+t) * alive i (a+t) + rho * (d (a+t) * b (a+t) * onlyY i j (a+t))) := by
           apply Finset.sum_congr rfl
           intro t ht
           ring
    _ = (∑ t ∈ Finset.range n, d (a+t) * b (a+t) * alive i (a+t)) +
         rho * (∑ t ∈ Finset.range n, d (a+t) * b (a+t) * onlyY i j (a+t)) := by
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

theorem solution (h a n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho : ℝ) :
    deferMemberSpouse h a n p d b rho = deferX h a n p d b + rho * deferRev h a n p d b := by
  unfold deferMemberSpouse deferX deferRev deferValue
  simp_rw [annRange_member_spouse_split]
  exact expect_scaled_add h p rho
    (fun i j => annRange a n d b (alive i))
    (fun i j => annRange a n d b (onlyY i j))
