-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.zero_mass_le_of_diagonal_variation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/76098e0a-b256-459b-a3dd-bdff2dd9a0e8

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutation_small_support_coarea
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutationVariation_zero_indicator_le
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_zero_support_card_le_half_of_singletons

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
    h * (Finset.univ.filter fun x : V => f x = 0).card ≤
      (B : ℝ) := by
  have hhalf := zero_support_card_le_half_of_singletons f hsingle
  have hcoarea := permutation_small_support_coarea
    σ h hexp (fun x => if f x = 0 then 1 else 0) hhalf
  have hcontract := permutationVariation_zero_indicator_le σ f
  have htotal :
      permutationVariation σ (fun x => if f x = 0 then 1 else 0) ≤
        2 * B := hcontract.trans hvariation
  have htotal_real :
      (permutationVariation σ
        (fun x => if f x = 0 then 1 else 0) : ℝ) ≤
          2 * (B : ℝ) := by
    exact_mod_cast htotal
  have hsum :
      (∑ x : V, if f x = 0 then 1 else 0) =
        (Finset.univ.filter fun x : V => f x = 0).card := by
    simp
  rw [hsum] at hcoarea
  linarith
end SoficGroups.KunThomFiberCoarea
