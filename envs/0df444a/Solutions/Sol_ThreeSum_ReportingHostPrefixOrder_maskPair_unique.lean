-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixOrder.maskPair_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:14:41.205277+00:00
-- url     : https://prove2.me/submissions/4e8a7bd0-4b56-4868-92a5-e3c0e184a5f8

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_prefixes_nodup
import Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_preL_get
import Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_preR_get
import Definitions.Def_WeightedCache3SUM_Alias_b81ece442bf7f0dc


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixOrder
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPairEnumeration
open ReportingHostPrefixMasks ReportingHostPairSegments
set_option maxHeartbeats 600000
namespace ThreeSum.ReportingHostPrefixOrder
theorem _root_.solution {h J k i j : ℕ} (hk : k ≤ J)
    (hi : i < (prefixes h k).length) (hj : j < (prefixes h k).length)
    (hL : subsetMask (preL h J k i) = subsetMask (preL h J k j))
    (hR : subsetMask (preR h J k i) = subsetMask (preR h J k j)) : i=j := by
  rw [preL_get hi,preL_get hj] at hL
  rw [preR_get hi,preR_get hj] at hR
  have he := maskPair_injective hk (Prod.ext hL hR)
  exact (prefixes_nodup h k).getElem_inj_iff.mp he
end ThreeSum.ReportingHostPrefixOrder
