-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixMasks.leftSet_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:03:23.388125+00:00
-- url     : https://prove2.me/submissions/a8b51abd-d470-4bf7-921a-981dbdb4950d

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
    subsetMask (leftSet (J := J) p) = ∑ i : Fin k, 2^(i.val*(512*h))*subsetMask (p i).val.1 := by
  unfold leftSet leftRows
  exact mask_rows_ofFin (J := J) (L := 512*h) (k := k) hk (fun i => (p i).val.1)
end ThreeSum.ReportingHostPrefixMasks
