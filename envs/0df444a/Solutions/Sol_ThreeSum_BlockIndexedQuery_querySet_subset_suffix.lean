-- Prove2me | solution 1 for ThreeSum.BlockIndexedQuery.querySet_subset_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:53:17.289187+00:00
-- url     : https://prove2.me/submissions/9ca21767-c37d-4255-bf5e-e3de1c372bbc

import Definitions.Def_Submission_ThreeSum_BlockIndex
import Definitions.Def_Submission_ThreeSum_StoredReporting
import Definitions.Def_Submission_ThreeSum_SubsetTransport
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Mathlib.Data.Fintype.Fin
import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_WeightedCache3SUM_Alias_66e44d153b23210a
import Theorems.Thm_ThreeSum_BlockIndex_indexSet_subset
import Theorems.Thm_ThreeSum_BlockRows_join_subset
attribute [local simp] ThreeSum.BlockIndex.indexSet_subset



set_option autoImplicit false
open ThreeSum ThreeSum.BlockIndexedQuery
open Finset BlockRows BlockIndex BlockForced BlockEncoding GlobalEncoding
open LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
namespace ThreeSum.BlockIndexedQuery
theorem _root_.solution {J L k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L)) :
    querySet k Q ⊆ SubsetStages.suffix (J*L) (suffixStage J L k) := by
  rw [← index_suffixDomain hk]
  exact (indexSet_subset _ _).mpr (join_subset _ (fun _ _ => Finset.subset_univ _))
end ThreeSum.BlockIndexedQuery
