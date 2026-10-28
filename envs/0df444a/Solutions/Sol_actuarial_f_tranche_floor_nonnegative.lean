-- Prove2me | solution 1 for actuarial_f_tranche_floor_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:39:06.648851+00:00
-- url     : https://prove2.me/submissions/261f4787-0f53-46e0-8cb9-af50e554a4a5

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_trancheFloorTotal

open ActuarialUnderpinsF

theorem solution (a b : ℕ → ℝ) (k : ℕ)
    (ha : ∀ i ∈ Finset.range k, 0 ≤ a i) :
    0 ≤ trancheFloorTotal a b k := by
  have sle : ∀ (s : Finset ℕ) (f g : ℕ → ℝ), (∀ x ∈ s, f x ≤ g x) → s.sum f ≤ s.sum g := by
    intro s f g hfg
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact add_le_add (hfg a (Finset.mem_insert_self a s)) (ih fun x hx => hfg x (Finset.mem_insert_of_mem hx))
  have := sle (Finset.range k) (fun _ => 0) (fun i => awardBase a b i) fun i hi => le_trans (ha i hi) (le_max_left _ _)
  simpa [trancheFloorTotal] using this
