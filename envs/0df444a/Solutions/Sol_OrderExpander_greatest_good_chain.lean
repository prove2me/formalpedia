-- Prove2me | solution 1 for OrderExpander.greatest_good_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:47:39.862544+00:00
-- url     : https://prove2.me/submissions/af05fb2d-66ca-495d-8a8a-6f242d4abaee

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
import Theorems.Thm_IsSegment_of_Subset
import Theorems.Thm_exists_strictBound_of_IsSegment
import Theorems.Thm_OrderExpander_IsChain_U
import Theorems.Thm_OrderExpander_IsSegment_U_of_Good

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
open OrderExpander
variable [PartialOrder α] [OrderExpander α]
namespace OrderExpander
theorem _root_.solution : Good (U (α := α)) := by
  constructor
  · exact IsChain_U
  · intro S Sprseg
    obtain ⟨d, d_in_U, d_sb⟩ := exists_strictBound_of_IsSegment S U Sprseg (IsChain_U)
    obtain ⟨D, Good_D, d_in_D⟩ := d_in_U
    dsimp at Good_D
    have DsegU := (IsSegment_U_of_Good Good_D)
    have SsubD : S ⊆ D := fun c cinS =>
      DsegU.2 c (Sprseg.1.1 cinS) d d_in_D <| le_of_lt <| d_sb c cinS
    have SprsegD : S ⊏ D := by
      constructor
      · exact IsSegment_of_Subset D U S DsegU.left Sprseg.1 SsubD
      · have : d ∉ S := by
          have := fun c (h : c ∈ S) => ne_of_lt <| d_sb c h
          tauto
        aesop
    have : (g S) ⊑ D := (Good_D.2 SprsegD).2
    exact ⟨(Good_D.2 SprsegD).1, IsSegment_trans this DsegU⟩
end OrderExpander
