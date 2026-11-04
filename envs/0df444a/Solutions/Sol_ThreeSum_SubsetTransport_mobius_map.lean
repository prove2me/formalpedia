-- Prove2me | solution 1 for ThreeSum.SubsetTransport.mobius_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:54.492236+00:00
-- url     : https://prove2.me/submissions/b1581d95-d43f-468d-9940-a6d7854281ed

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetTransport
import Theorems.Thm_ThreeSum_SubsetTransport_reindex_map
import Theorems.Thm_ThreeSum_SubsetTransport_sum_powerset_map
attribute [local simp] ThreeSum.SubsetTransport.reindex_map

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetTransport
open Finset
open scoped BigOperators
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
namespace ThreeSum.SubsetTransport
theorem _root_.solution (e : α ≃ β) (f : Finset α → ℤ) (S : Finset α) :
    Subset.mobius (reindex e f) (S.map e.toEmbedding) = Subset.mobius f S := by
  unfold Subset.mobius
  rw [sum_powerset_map]
  simp only [Finset.card_map,reindex_map]
end ThreeSum.SubsetTransport
