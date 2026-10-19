-- Prove2me | solution 1 for SoficGroups.KunFinitePermutationMarkovMass.sum_realPermutationMarkov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/af856b59-4182-4b94-9126-69e6547dca46

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunFinitePermutationMarkovMass
open scoped BigOperators
namespace SoficGroups.KunFinitePermutationMarkovMass
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) :
    (∑ x : V, realPermutationMarkov σ f x) = ∑ x : V, f x := by
  classical
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    (∑ x : V, realPermutationMarkov σ f x) =
        (Fintype.card ι : ℝ)⁻¹ *
          ∑ i : ι, ∑ x : V, f ((σ i).symm x) := by
      simp only [realPermutationMarkov, ← Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = (Fintype.card ι : ℝ)⁻¹ *
          ∑ i : ι, ∑ x : V, f x := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp (σ i).symm f
    _ = ∑ x : V, f x := by
      simp [hcard]
end SoficGroups.KunFinitePermutationMarkovMass
