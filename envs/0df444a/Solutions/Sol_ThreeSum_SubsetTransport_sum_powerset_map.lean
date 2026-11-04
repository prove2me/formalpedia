-- Prove2me | solution 1 for ThreeSum.SubsetTransport.sum_powerset_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:09:19.455201+00:00
-- url     : https://prove2.me/submissions/1cdc8a75-d05d-4f33-98f0-ac2b6ba6c444

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetTransport
import Theorems.Thm_ThreeSum_SubsetTransport_reindex_map
attribute [local simp] ThreeSum.SubsetTransport.reindex_map

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetTransport
open Finset
open scoped BigOperators
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
namespace ThreeSum.SubsetTransport
theorem _root_.solution (e : α ≃ β) (S : Finset α) (f : Finset β → ℤ) :
    (∑ T ∈ (S.map e.toEmbedding).powerset, f T) =
      ∑ T ∈ S.powerset, f (T.map e.toEmbedding) := by
  simp only [Finset.map_eq_image]
  rw [Finset.powerset_image,Finset.sum_image]
  intro A hA B hB he
  exact (Finset.image_inj e.injective).mp he
end ThreeSum.SubsetTransport
