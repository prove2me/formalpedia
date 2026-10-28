-- Prove2me | solution 1 for actuarial_f_tranche_floor_dominates_second
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:38:59.078237+00:00
-- url     : https://prove2.me/submissions/9bd86eca-4e08-4935-8fe9-ce504e466a35

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_trancheFloorTotal

open ActuarialUnderpinsF

theorem solution (a b : ℕ → ℝ) (k : ℕ) :
    (∑ i ∈ Finset.range k, b i) ≤ trancheFloorTotal a b k := by
  have sle : ∀ (s : Finset ℕ) (f g : ℕ → ℝ), (∀ x ∈ s, f x ≤ g x) → s.sum f ≤ s.sum g := by
    intro s f g hfg
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact add_le_add (hfg a (Finset.mem_insert_self a s)) (ih fun x hx => hfg x (Finset.mem_insert_of_mem hx))
  exact sle _ _ _ fun i _ => le_max_right _ _
