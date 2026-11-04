-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixMasks.rightSet_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:03:24.670031+00:00
-- url     : https://prove2.me/submissions/3e49b826-d8de-4879-89ee-238f92863c6c

import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Theorems.Thm_ThreeSum_ReportingHostPrefixMasks_mask_rows_ofFin

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixMasks
open Finset ThreeSum.SubsetAddress BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open BlockForced
open ReportingHostPrefixCatalog ReportingHostPairEnumeration
open scoped BigOperators
set_option maxHeartbeats 500000
variable {α : Type*}
namespace ThreeSum.ReportingHostPrefixMasks
theorem _root_.solution {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    subsetMask (rightSet (J := J) p) = ∑ i : Fin k, 2^(i.val*(512*h))*subsetMask (p i).val.2 := by
  unfold rightSet rightRows
  exact mask_rows_ofFin (J := J) (L := 512*h) (k := k) hk (fun i => (p i).val.2)
end ThreeSum.ReportingHostPrefixMasks
