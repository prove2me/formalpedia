-- Prove2me | solution 1 for ThreeSum.SubsetTransport.mobius_partial_product_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:35:28.679092+00:00
-- url     : https://prove2.me/submissions/f5a8e188-401a-40a4-b198-a6c19fb9b1ca

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetTransport
import Theorems.Thm_ThreeSum_SubsetTransport_reindex_map
import Theorems.Thm_ThreeSum_SubsetTransport_sum_powerset_map
import Theorems.Thm_ThreeSum_SubsetTransport_partialZeta_map
attribute [local simp] ThreeSum.SubsetTransport.reindex_map

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetTransport
open Finset
open scoped BigOperators
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
namespace ThreeSum.SubsetTransport
theorem _root_.solution (e : α ≃ β) (f g : Finset α → ℤ)
    (processed preL preR Q : Finset α) :
    Subset.mobius (fun S =>
      Subset.partialZeta (processed.map e.toEmbedding) (reindex e f) (preL.map e.toEmbedding ∪ S) *
      Subset.partialZeta (processed.map e.toEmbedding) (reindex e g) (preR.map e.toEmbedding ∪ S))
      (Q.map e.toEmbedding) =
      Subset.mobius (fun S => Subset.partialZeta processed f (preL ∪ S) *
        Subset.partialZeta processed g (preR ∪ S)) Q := by
  unfold Subset.mobius
  rw [sum_powerset_map]
  simp only [← Finset.map_union,partialZeta_map,Finset.card_map]
end ThreeSum.SubsetTransport
