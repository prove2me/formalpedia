-- Prove2me | solution 1 for ThreeSum.SubsetTransport.partialZeta_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:31:50.885517+00:00
-- url     : https://prove2.me/submissions/4a397ea8-0624-4d7d-838b-741690fe9ce8

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
theorem _root_.solution (e : α ≃ β) (f : Finset α → ℤ) (processed S : Finset α) :
    Subset.partialZeta (processed.map e.toEmbedding) (reindex e f) (S.map e.toEmbedding) =
      Subset.partialZeta processed f S := by
  unfold Subset.partialZeta
  rw [← Finset.map_inter,sum_powerset_map]
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Finset.map_sdiff,← Finset.map_union,reindex_map]
end ThreeSum.SubsetTransport
