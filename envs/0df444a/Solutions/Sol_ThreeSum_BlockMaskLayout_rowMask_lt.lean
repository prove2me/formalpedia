-- Prove2me | solution 1 for ThreeSum.BlockMaskLayout.rowMask_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:50:29.998821+00:00
-- url     : https://prove2.me/submissions/f4e1e6a6-9c44-4659-a8b7-3e19a2a84ac0

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Theorems.Thm_ThreeSum_BlockMaskLayout_prefixMask_succ
import Theorems.Thm_ThreeSum_BlockMaskLayout_prefixMask_lt

set_option autoImplicit false
open ThreeSum ThreeSum.BlockMaskLayout
open Finset BlockRows BlockIndex ThreeSum.SubsetAddress
open scoped BigOperators
namespace ThreeSum.BlockMaskLayout
theorem _root_.solution {J L : ℕ} (rows : Fin J → Finset (Fin L)) (i : Fin J) :
    rowMask rows i < 2^(J*L) := by
  have he : prefixMask rows (i.val+1) = prefixMask rows i.val+rowMask rows i :=
    prefixMask_succ rows i.isLt
  have hb := prefixMask_lt rows (i.val+1)
  omega
end ThreeSum.BlockMaskLayout
