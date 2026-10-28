-- Prove2me | solution 1 for actuarial_f_expected_award_at_least_first
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:36:35.214448+00:00
-- url     : https://prove2.me/submissions/5460e322-443e-4c8c-9814-8a36387d1827

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase
import Definitions.Def_actuarial_f_expect

open ActuarialUnderpinsF

theorem solution (n h : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ) (a b : ℕ → ℝ)
    (hp : ∀ z ∈ Finset.range n, ∀ i ∈ Finset.range (h+1),
      ∀ j ∈ Finset.range (h+1), 0 ≤ p z i j) :
    expect n h p (fun z i j => a z) ≤
      expect n h p (fun z i j => awardBase a b z) := by
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
  exact mul_le_mul_of_nonneg_left (le_max_left _ _) (hp z hz i hi j hj)
