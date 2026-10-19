-- Prove2me | solution 1 for SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov_iterate_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/ddb7e66b-f46d-46ee-85aa-c91ffa4fbcad

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunFinitePermutationMarkovMass_realPermutationMarkov_le_one

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunFinitePermutationMarkovMass
open scoped BigOperators
namespace SoficGroups.KunFinitePermutationMarkovMass
theorem _root_.solution {V ι : Type*}
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, f x ≤ 1) (k : ℕ) :
    ∀ x, ((realPermutationMarkov σ)^[k]) f x ≤ 1 := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    intro x
    rw [Function.iterate_succ_apply']
    exact realPermutationMarkov_le_one σ _ ih x
end SoficGroups.KunFinitePermutationMarkovMass
