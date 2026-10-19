-- Prove2me | solution 1 for SoficGroups.KunActualFinalRestrictedVariation.highSupport_variation_le_of_realMarkov_residual_and_highSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/7a94e2e9-9480-4f73-937b-0f5ac79737de

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_sum_sum_sq_displacement_le_twice_card_mul_sqrt_card_mul_residual
import Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_highSupport_variation_sq_le_three_mul_reference_energy
import Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_high_variation_le_of_markov_square_bounds

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators
namespace SoficGroups.KunActualFinalRestrictedVariation
theorem _root_.solution
    {V ι : Type*} [Fintype V]
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (T : Finset V) (f : V → ℝ)
    (α η b : ℝ)
    (hfzero : ∀ x, 0 ≤ f x) (hfone : ∀ x, f x ≤ 1)
    (hmass : (∑ x : V, f x) = (T.card : ℝ))
    (hhigh :
      ((Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x)).card : ℝ) ≤
          3 * (T.card : ℝ))
    (hα : 0 ≤ α) (hη : 0 ≤ η)
    (hbase : b ^ 2 ≤ (T.card : ℝ))
    (hresidual :
      Real.sqrt (∑ x : V,
        (realMarkov σ f x - f x) ^ 2) ≤ η * b)
    (hsmall :
      486 * (Fintype.card ι : ℝ) ^ 2 * η ≤ 4 * α ^ 2) :
    9 * (∑ i : ι,
      ∑ x ∈ Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x),
          |f (σ i x) - f x|) ≤ 2 * α * (T.card : ℝ) := by
  exact high_variation_le_of_markov_square_bounds
    (d := (Fintype.card ι : ℝ))
    (t := (T.card : ℝ))
    (α := α) (η := η) (b := b)
    (r := Real.sqrt (∑ x : V,
      (realMarkov σ f x - f x) ^ 2))
    (E := ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2)
    (H := ∑ i : ι,
      ∑ x ∈ Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x),
          |f (σ i x) - f x|)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hα hη hbase hresidual
    (sum_sum_sq_displacement_le_twice_card_mul_sqrt_card_mul_residual
      σ T f hfzero hfone hmass)
    (highSupport_variation_sq_le_three_mul_reference_energy
      σ f T hhigh)
    hsmall
end SoficGroups.KunActualFinalRestrictedVariation
