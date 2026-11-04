-- Prove2me | solution 1 for ThreeSum.BlockSourceTableLayout.mask_sets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:05:39.642705+00:00
-- url     : https://prove2.me/submissions/f20bba16-8a44-4a0e-8d7f-27d264d035c4

import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_BlockSourceTableLayout
import Theorems.Thm_ThreeSum_BlockIndex_index_unindex
import Theorems.Thm_ThreeSum_SourceTableLayout_subsetMask_setAt
attribute [local simp] ThreeSum.BlockIndex.index_unindex



set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceTableLayout
open SubsetAddress BlockIndex BlockEncoding BlockRows GlobalEncoding
namespace ThreeSum.BlockSourceTableLayout
theorem _root_.solution {h J cut i : ℕ} (hi : i < downsetCap (J*(512*h)) cut) :
    subsetMask (indexSet (sets h J cut i)) = SourceTableLayout.maskAt (J*(512*h)) cut i := by
  rw [sets,index_unindex,SourceTableLayout.subsetMask_setAt hi]
end ThreeSum.BlockSourceTableLayout
