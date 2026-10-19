-- Prove2me | solution 1 for SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov_iterate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/0a2f7c07-b599-49ea-bdba-07a2daebea69

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunFinitePermutationMarkovMass_realPermutationMarkov_nonneg

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunFinitePermutationMarkovMass
open scoped BigOperators
namespace SoficGroups.KunFinitePermutationMarkovMass
theorem _root_.solution {V ι : Type*}
    [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) (k : ℕ) :
    ∀ x, 0 ≤ ((realPermutationMarkov σ)^[k]) f x := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    intro x
    rw [Function.iterate_succ_apply']
    exact realPermutationMarkov_nonneg σ _ ih x
end SoficGroups.KunFinitePermutationMarkovMass
