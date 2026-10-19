-- Prove2me | solution 1 for SoficGroups.KunActualFinalRestrictedVariation.filtered_variation_sq_le_card_mul_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/f00ad5b0-e30e-46c7-91b6-1d764a28033b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_filtered_variation_sq_le_card_mul_filtered_energy

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators
namespace SoficGroups.KunActualFinalRestrictedVariation
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (H : Finset V) :
    (∑ i : ι, ∑ x ∈ H, |f (σ i x) - f x|) ^ 2 ≤
      (Fintype.card ι : ℝ) * (H.card : ℝ) *
        ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 := by
  classical
  have henergy :
      (∑ i : ι, ∑ x ∈ H, (f (σ i x) - f x) ^ 2) ≤
        ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ H)
    intro x _ _
    exact sq_nonneg _
  calc
    (∑ i : ι, ∑ x ∈ H, |f (σ i x) - f x|) ^ 2 ≤
        (Fintype.card ι : ℝ) * (H.card : ℝ) *
          ∑ i : ι, ∑ x ∈ H, (f (σ i x) - f x) ^ 2 :=
      filtered_variation_sq_le_card_mul_filtered_energy σ f H
    _ ≤ (Fintype.card ι : ℝ) * (H.card : ℝ) *
          ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 :=
      mul_le_mul_of_nonneg_left henergy
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
end SoficGroups.KunActualFinalRestrictedVariation
