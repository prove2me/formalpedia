-- Prove2me | solution 1 for ThreeSum.SubsetTransport.reindex_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:52:20.192768+00:00
-- url     : https://prove2.me/submissions/7dc97b02-cc6e-4ad9-b96c-de1f5ee62067

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetTransport

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetTransport
open Finset
open scoped BigOperators
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
namespace ThreeSum.SubsetTransport
theorem _root_.solution (e : α ≃ β) (f : Finset α → ℤ) (S : Finset α) :
    reindex e f (S.map e.toEmbedding) = f S := by
  unfold reindex
  congr 1
  ext a
  simp
end ThreeSum.SubsetTransport
