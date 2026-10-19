-- Prove2me | solution 1 for SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/f83ecdeb-c3fe-45c1-8e91-ad93f60d990e

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunFinitePermutationMarkovMass
open scoped BigOperators
namespace SoficGroups.KunFinitePermutationMarkovMass
theorem _root_.solution {V ι : Type*}
    [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) (x : V) :
    0 ≤ realPermutationMarkov σ f x := by
  unfold realPermutationMarkov
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ => hf ((σ i).symm x))
end SoficGroups.KunFinitePermutationMarkovMass
