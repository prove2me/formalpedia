-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.permutationVariation_zero_indicator_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/6f2fd4be-b47a-4655-9bd3-732798d9c056

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_natDist_zero_indicator_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℕ) :
    permutationVariation σ (fun x => if f x = 0 then 1 else 0) ≤
      permutationVariation σ f := by
  unfold permutationVariation
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro x _
  exact natDist_zero_indicator_le (f (σ i x)) (f x)
end SoficGroups.KunThomFiberCoarea
