-- Prove2me | solution 1 for ThreeSum.BlockIndexedQuery.leftPrefix_disjoint_query
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:37:41.177983+00:00
-- url     : https://prove2.me/submissions/d74bf614-743d-4367-b362-ec03fff12f7f

import Definitions.Def_Submission_ThreeSum_BlockIndex
import Definitions.Def_Submission_ThreeSum_StoredReporting
import Definitions.Def_Submission_ThreeSum_SubsetTransport
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Mathlib.Data.Fintype.Fin
import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Theorems.Thm_ThreeSum_BlockRows_join_disjoint_compl


set_option autoImplicit false
open ThreeSum ThreeSum.BlockIndexedQuery
open Finset BlockRows BlockIndex BlockForced BlockEncoding GlobalEncoding
open LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
namespace ThreeSum.BlockIndexedQuery
theorem _root_.solution {J L : ℕ} (k : ℕ) (Q u : Fin J → Finset (Fin L)) :
    Disjoint (leftPrefix k u) (querySet k Q) := by
  exact (Finset.disjoint_map _).mpr (join_disjoint_compl (prefixIndices J k) u Q)
end ThreeSum.BlockIndexedQuery
