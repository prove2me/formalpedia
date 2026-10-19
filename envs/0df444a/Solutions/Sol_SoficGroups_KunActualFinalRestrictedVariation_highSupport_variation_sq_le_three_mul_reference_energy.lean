-- Prove2me | solution 1 for SoficGroups.KunActualFinalRestrictedVariation.highSupport_variation_sq_le_three_mul_reference_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/87a74947-c288-4d7e-8b29-f58bc37fe400

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_filtered_variation_sq_le_card_mul_energy

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators
namespace SoficGroups.KunActualFinalRestrictedVariation
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (T : Finset V)
    (hhigh :
      ((Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x)).card : ℝ) ≤
          3 * (T.card : ℝ)) :
    (∑ i : ι,
      ∑ x ∈ Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x),
          |f (σ i x) - f x|) ^ 2 ≤
      3 * (Fintype.card ι : ℝ) * (T.card : ℝ) *
        ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 := by
  have henergy :
      0 ≤ ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 :=
    Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun x _ => sq_nonneg _
  calc
    (∑ i : ι,
      ∑ x ∈ Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x),
          |f (σ i x) - f x|) ^ 2 ≤
        (Fintype.card ι : ℝ) *
          ((Finset.univ.filter
            (fun x : V => (1 / 3 : ℝ) < f x)).card : ℝ) *
          ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 :=
      filtered_variation_sq_le_card_mul_energy σ f
        (Finset.univ.filter fun x : V => (1 / 3 : ℝ) < f x)
    _ ≤ (Fintype.card ι : ℝ) * (3 * (T.card : ℝ)) *
        ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hhigh (Nat.cast_nonneg _)) henergy
    _ = 3 * (Fintype.card ι : ℝ) * (T.card : ℝ) *
        ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 := by
      ring
end SoficGroups.KunActualFinalRestrictedVariation
