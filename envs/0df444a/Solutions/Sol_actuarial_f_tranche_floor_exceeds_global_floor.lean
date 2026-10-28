-- Prove2me | solution 1 for actuarial_f_tranche_floor_exceeds_global_floor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:39:03.226995+00:00
-- url     : https://prove2.me/submissions/91a2879e-1658-4753-afc2-c49f2271d83c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_trancheFloorTotal
import Definitions.Def_actuarial_f_wholeFloorTotal

open ActuarialUnderpinsF

theorem solution (a b : ℕ → ℝ) (k : ℕ) :
    wholeFloorTotal a b k ≤ trancheFloorTotal a b k := by
  have sle : ∀ (s : Finset ℕ) (f g : ℕ → ℝ), (∀ x ∈ s, f x ≤ g x) → s.sum f ≤ s.sum g := by
    intro s f g hfg
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact add_le_add (hfg a (Finset.mem_insert_self a s)) (ih fun x hx => hfg x (Finset.mem_insert_of_mem hx))
  unfold wholeFloorTotal
  exact max_le (sle _ _ _ fun i _ => le_max_left _ _) (sle _ _ _ fun i _ => le_max_right _ _)
