-- Prove2me | solution 1 for actuarial_f_expect_mono
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:32:11.062221+00:00
-- url     : https://prove2.me/submissions/d21e608d-81e8-49ac-bfea-bdb683f591b9

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect

open ActuarialUnderpinsF

theorem solution (n h : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (f g : ℕ → ℕ → ℕ → ℝ)
    (hp : ∀ z ∈ Finset.range n, ∀ i ∈ Finset.range (h+1),
      ∀ j ∈ Finset.range (h+1), 0 ≤ p z i j)
    (hfg : ∀ z ∈ Finset.range n, ∀ i ∈ Finset.range (h+1),
      ∀ j ∈ Finset.range (h+1), f z i j ≤ g z i j) :
    expect n h p f ≤ expect n h p g := by
  have sle : ∀ (s : Finset ℕ) (f g : ℕ → ℝ), (∀ x ∈ s, f x ≤ g x) → s.sum f ≤ s.sum g := by
    intro s f g hfg
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact add_le_add (hfg a (Finset.mem_insert_self a s)) (ih fun x hx => hfg x (Finset.mem_insert_of_mem hx))
  unfold expect ActuarialJointD.expect
  apply sle; intro z hz
  apply sle; intro i hi
  apply sle; intro j hj
  exact mul_le_mul_of_nonneg_left (hfg z hz i hi j hj) (hp z hz i hi j hj)
