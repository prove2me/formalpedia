-- Prove2me | solution 1 for ThreeSum.BlockMaskLayout.prefixMask_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:05:41.977702+00:00
-- url     : https://prove2.me/submissions/9ee78aae-7109-4c36-be7b-c706899ffa65

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Theorems.Thm_ThreeSum_BlockMaskLayout_mask_join

set_option autoImplicit false
open ThreeSum ThreeSum.BlockMaskLayout
open Finset BlockRows BlockIndex ThreeSum.SubsetAddress
open scoped BigOperators
namespace ThreeSum.BlockMaskLayout
theorem _root_.solution {J L : ℕ} (rows : Fin J → Finset (Fin L)) (k : ℕ) :
    prefixMask rows k = ∑ i ∈ prefixIndices J k, rowMask rows i := mask_join _ _
end ThreeSum.BlockMaskLayout
