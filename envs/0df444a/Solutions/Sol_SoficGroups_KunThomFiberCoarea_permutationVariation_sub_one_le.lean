-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.permutationVariation_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/38479eaf-c5c6-4a96-bed2-e235345ee3d2

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_natDist_sub_one_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℕ) :
    permutationVariation σ (fun x => f x - 1) ≤
      permutationVariation σ f := by
  unfold permutationVariation
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro x _
  exact natDist_sub_one_le (f (σ i x)) (f x)
end SoficGroups.KunThomFiberCoarea
