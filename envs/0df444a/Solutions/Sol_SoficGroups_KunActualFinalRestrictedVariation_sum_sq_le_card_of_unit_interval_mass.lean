-- Prove2me | solution 1 for SoficGroups.KunActualFinalRestrictedVariation.sum_sq_le_card_of_unit_interval_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/dc474ce3-7d53-4f55-9464-32b59f1d0c9a

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators
namespace SoficGroups.KunActualFinalRestrictedVariation
theorem _root_.solution
    {V : Type*} [Fintype V]
    (T : Finset V) (f : V → ℝ)
    (hfzero : ∀ x, 0 ≤ f x) (hfone : ∀ x, f x ≤ 1)
    (hmass : (∑ x : V, f x) = (T.card : ℝ)) :
    (∑ x : V, f x ^ 2) ≤ (T.card : ℝ) := by
  calc
    (∑ x : V, f x ^ 2) ≤ ∑ x : V, f x := by
      apply Finset.sum_le_sum
      intro x _
      nlinarith [mul_nonneg (hfzero x)
        (sub_nonneg.mpr (hfone x))]
    _ = (T.card : ℝ) := hmass
end SoficGroups.KunActualFinalRestrictedVariation
