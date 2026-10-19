-- Prove2me | solution 1 for SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/87e9574e-a65c-4d7d-8fca-f8c411bdcb12

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunFinitePermutationMarkovMass
open scoped BigOperators
namespace SoficGroups.KunFinitePermutationMarkovMass
theorem _root_.solution {V ι : Type*}
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, f x ≤ 1) (x : V) :
    realPermutationMarkov σ f x ≤ 1 := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum :
      (∑ i : ι, f ((σ i).symm x)) ≤ ∑ _i : ι, (1 : ℝ) := by
    exact Finset.sum_le_sum fun i _ => hf ((σ i).symm x)
  calc
    realPermutationMarkov σ f x =
        (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, f ((σ i).symm x) := rfl
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left hsum
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = 1 := by
      simp [hcard]
end SoficGroups.KunFinitePermutationMarkovMass
