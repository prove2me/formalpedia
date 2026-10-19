-- Prove2me | solution 1 for SoficGroups.KunActualFinalRestrictedVariation.sum_sum_sq_displacement_le_twice_card_mul_sqrt_card_mul_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/21b64971-3c9b-408a-829d-fdc3ef5d4382

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_sum_sum_sq_displacement_eq_twice_card_mul_realMarkov_residual
import Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_realMarkov_residual_pairing_le_sqrt_card_mul_residual

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
    (hfzero : ∀ x, 0 ≤ f x) (hfone : ∀ x, f x ≤ 1)
    (hmass : (∑ x : V, f x) = (T.card : ℝ)) :
    (∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2) ≤
      2 * (Fintype.card ι : ℝ) * Real.sqrt (T.card : ℝ) *
        Real.sqrt (∑ x : V,
          (realMarkov σ f x - f x) ^ 2) := by
  rw [sum_sum_sq_displacement_eq_twice_card_mul_realMarkov_residual]
  have hpair := realMarkov_residual_pairing_le_sqrt_card_mul_residual
    σ T f hfzero hfone hmass
  have hfactor : 0 ≤ 2 * (Fintype.card ι : ℝ) := by positivity
  nlinarith [mul_nonneg hfactor
    (sub_nonneg.mpr hpair)]
end SoficGroups.KunActualFinalRestrictedVariation
