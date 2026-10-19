-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.excess_mass_le_of_diagonal_variation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/e0212a5b-314b-4aad-93b5-b9e438afd450

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutation_small_support_coarea
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutationVariation_sub_one_le
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_excess_support_card_le_half_of_singletons

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (h : ℝ)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ))
    (f : V → ℕ) (B : ℕ)
    (hsingle : Fintype.card V ≤ 2 * (singletonSupport f).card)
    (hvariation : permutationVariation σ f ≤ 2 * B) :
    h * (∑ x : V, (f x - 1 : ℕ)) ≤ (B : ℝ) := by
  have hhalf := excess_support_card_le_half_of_singletons f hsingle
  have hcoarea := permutation_small_support_coarea
    σ h hexp (fun x => f x - 1) hhalf
  have hcontract := permutationVariation_sub_one_le σ f
  have htotal :
      permutationVariation σ (fun x => f x - 1) ≤ 2 * B :=
    hcontract.trans hvariation
  have htotal_real :
      (permutationVariation σ (fun x => f x - 1) : ℝ) ≤
        2 * (B : ℝ) := by
    exact_mod_cast htotal
  linarith
end SoficGroups.KunThomFiberCoarea
