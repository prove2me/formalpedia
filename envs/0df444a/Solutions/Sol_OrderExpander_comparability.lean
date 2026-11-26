-- Prove2me | solution 1 for OrderExpander.comparability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:46:29.41734+00:00
-- url     : https://prove2.me/submissions/09993ed9-563c-480a-b272-684c8398d4aa

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
import Theorems.Thm_sUnion_of_IsSegment
import Theorems.Thm_OrderExpander_ssubset_g

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
open OrderExpander
variable [PartialOrder α] [OrderExpander α]
namespace OrderExpander
theorem _root_.solution (C D : Set α) (goodC : Good C) (goodD : Good D) :
    C ⊑ D ∨ D ⊑ C := by
  let S := {M : Set α | M ⊑ C ∧ M ⊑ D}
  have segs : (∀ M ∈ S, M ⊑ C) ∧ (∀ M ∈ S, M ⊑ D) :=
    ⟨fun M hM => hM.1, fun M hM => hM.2⟩
  have UnSseg : (⋃₀ S) ⊑ C ∧ (⋃₀ S) ⊑ D :=
    ⟨sUnion_of_IsSegment segs.1, sUnion_of_IsSegment segs.2⟩
  by_contra incomp ; push Not at incomp
  have UnSne: ⋃₀ S ≠ C ∧ ⋃₀ S ≠ D := by aesop
  have UnSprsegC : ⋃₀ S ⊏ C := ⟨UnSseg.1, UnSne.1⟩
  have succ_segC : (g (⋃₀ S)) ⊑ C := (goodC.2 ⟨UnSseg.1, UnSne.1⟩).2
  have succ_segD : (g (⋃₀ S)) ⊑ D := (goodD.2 ⟨UnSseg.2, UnSne.2⟩).2
  have : g (⋃₀ S) ⊆ ⋃₀ S := subset_sUnion_of_subset _ _ (Eq.subset rfl) $
    mem_sep succ_segC succ_segD
  exact not_subset_of_ssubset (ssubset_g goodC UnSprsegC) this
end OrderExpander
