-- Prove2me | solution 1 for SoficGroups.KunFinitePermutationMarkovMass.sum_realPermutationMarkov_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/f94b28d1-2160-40ce-86be-a4feff09ed73

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunFinitePermutationMarkovMass_sum_realPermutationMarkov

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunFinitePermutationMarkovMass
open scoped BigOperators
namespace SoficGroups.KunFinitePermutationMarkovMass
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (k : ℕ) :
    (∑ x : V, ((realPermutationMarkov σ)^[k]) f x) =
      ∑ x : V, f x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (sum_realPermutationMarkov σ
      (((realPermutationMarkov σ)^[k]) f)).trans ih
end SoficGroups.KunFinitePermutationMarkovMass
