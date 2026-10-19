-- Prove2me | solution 1 for SoficGroups.KunActualFinalRestrictedVariation.highSupport_variation_le_of_realMarkov_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/ed827a61-17ac-4c61-a750-68dfe2c6c018

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_card_highSupport_le_three_card
import Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_highSupport_variation_le_of_realMarkov_residual_and_highSupport

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
  exact highSupport_variation_le_of_realMarkov_residual_and_highSupport
    σ T f α η b hfzero hfone hmass
    (card_highSupport_le_three_card T f hfzero hmass)
    hα hη hbase hresidual hsmall
end SoficGroups.KunActualFinalRestrictedVariation
