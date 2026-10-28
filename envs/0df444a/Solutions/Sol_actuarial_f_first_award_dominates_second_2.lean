-- Prove2me | solution 2 for actuarial_f_first_award_dominates_second
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:37:09.806075+00:00
-- url     : https://prove2.me/submissions/ef195c6d-1c96-444e-aa9d-39a073bfba2d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_firstAwardPV
import Definitions.Def_actuarial_f_firstOptionPV

open ActuarialUnderpinsF

theorem solution (n h r : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ) (disc a b growth : ℕ → ℝ)
    (hp : ∀ z ∈ Finset.range n, ∀ i ∈ Finset.range (h+1),
      ∀ j ∈ Finset.range (h+1), 0 ≤ p z i j)
    (hd : ∀ t ∈ Finset.range (h+1), 0 ≤ disc t)
    (hg : ∀ t ∈ Finset.range (h+1), 0 ≤ growth t) :
    firstOptionPV n h r p disc b growth ≤
      firstAwardPV n h r p disc a b growth := by
  have sle : ∀ (s : Finset ℕ) (f g : ℕ → ℝ), (∀ x ∈ s, f x ≤ g x) → s.sum f ≤ s.sum g := by
    intro s f g hfg
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact add_le_add (hfg a (Finset.mem_insert_self a s)) (ih fun x hx => hfg x (Finset.mem_insert_of_mem hx))
  have hm : ∀ i t : ℕ, 0 ≤ memberDue r i t := by
    intro i t; unfold memberDue ActuarialJointD.alive; split_ifs <;> norm_num
  unfold firstAwardPV firstOptionPV expect ActuarialJointD.expect
  apply sle; intro z hz
  apply sle; intro i hi
  apply sle; intro j hj
  refine mul_le_mul_of_nonneg_left ?_ (hp z hz i hi j hj)
  apply sle; intro t ht
  refine mul_le_mul_of_nonneg_left ?_ (hd t ht)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (hg t ht)) (hm i t)
