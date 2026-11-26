-- Prove2me | solution 1 for OrderSelector.good_of_isSegment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:46:35.350574+00:00
-- url     : https://prove2.me/submissions/97934b93-25e5-4441-af82-763aa9d40a56

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
import Theorems.Thm_IsSegment_of_Subset
import Theorems.Thm_IsSegment_total

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
variable [PartialOrder α] [OrderSelector α]
open OrderExpander
open OrderSelector
namespace OrderSelector
theorem _root_.solution {C D : Set α} (hC : Good C) (hseg : D ⊑ C) : Good D := by
  constructor
  · exact hC.1.mono hseg.1                      -- D is a chain: restriction of C's chain property
  · intro S hSD
    have hSC : S ⊏ C := IsPropSegment_of_IsPropSegment_of_IsSegment hSD hseg
    have goodS := hC.2 hSC                      -- S ⊏ g S ∧ g S ⊑ C
    rcases IsSegment_total hC.1 goodS.2 hseg with hgD | DgS
    · exact ⟨goodS.1, hgD⟩                      -- dichotomy case 1: done directly
    · -- case 2: D ⊑ g S; S ⊊ D forces f S ∈ D, hence g S ⊆ D
      obtain ⟨d, hdD, hdS⟩ := exists_of_ssubset (ssubset_of_IsPropSegment hSD)
      have hdgS : d ∈ g S := DgS.1 hdD
      have hdfS : d = f S := by
        rw [g_def] at hdgS
        rcases mem_or_mem_of_mem_union hdgS with h' | h'
        · exact absurd h' hdS
        · exact mem_singleton_iff.mp h'
      have hfSD : f S ∈ D := by rw [← hdfS]; exact hdD
      have hgD : g S ⊆ D := by
        rw [g_def]
        exact union_subset hSD.1.1 (show {f S} ⊆ D from fun c hc => by
          rw [mem_singleton_iff] at hc; rw [hc]; exact hfSD)
      exact ⟨goodS.1, IsSegment_of_Subset D C (g S) hseg.1 goodS.2 hgD⟩
end OrderSelector
