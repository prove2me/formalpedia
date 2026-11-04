-- Prove2me | solution 1 for ThreeSum.SubsetTransport.zeta_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:53.097773+00:00
-- url     : https://prove2.me/submissions/963905e2-7caf-4b41-9a7d-3e6069bbe6cf

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
    Subset.zeta (reindex e f) (S.map e.toEmbedding) = Subset.zeta f S := by
  unfold Subset.zeta
  rw [sum_powerset_map]
  simp only [reindex_map]
end ThreeSum.SubsetTransport
