-- Prove2me | solution 1 for SoficGroups.KunActualFinalRestrictedVariation.realMarkov_residual_pairing_le_sqrt_card_mul_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/064c7c80-98c2-41d5-9e75-7a30347502b0

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_sum_sq_le_card_of_unit_interval_mass

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators
namespace SoficGroups.KunActualFinalRestrictedVariation
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (T : Finset V) (f : V → ℝ)
    (hfzero : ∀ x, 0 ≤ f x) (hfone : ∀ x, f x ≤ 1)
    (hmass : (∑ x : V, f x) = (T.card : ℝ)) :
    (∑ x : V, f x * (f x - realMarkov σ f x)) ≤
      Real.sqrt (T.card : ℝ) *
        Real.sqrt (∑ x : V,
          (realMarkov σ f x - f x) ^ 2) := by
  have hsquare := sum_sq_le_card_of_unit_interval_mass
    T f hfzero hfone hmass
  calc
    (∑ x : V, f x * (f x - realMarkov σ f x)) ≤
        Real.sqrt (∑ x : V, f x ^ 2) *
          Real.sqrt (∑ x : V,
            (f x - realMarkov σ f x) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ f
        (fun x => f x - realMarkov σ f x)
    _ ≤ Real.sqrt (T.card : ℝ) *
          Real.sqrt (∑ x : V,
            (f x - realMarkov σ f x) ^ 2) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsquare)
        (Real.sqrt_nonneg _)
    _ = Real.sqrt (T.card : ℝ) *
          Real.sqrt (∑ x : V,
            (realMarkov σ f x - f x) ^ 2) := by
      congr 2
      apply Finset.sum_congr rfl
      intro x _
      ring
end SoficGroups.KunActualFinalRestrictedVariation
