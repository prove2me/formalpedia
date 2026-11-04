-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixOrder.preR_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:11:35.402981+00:00
-- url     : https://prove2.me/submissions/ceceddab-1719-4826-98dd-62bd94e7b0af

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_preR_get
import Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_rightSet_card


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixOrder
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPairEnumeration
open ReportingHostPrefixMasks ReportingHostPairSegments
set_option maxHeartbeats 600000
namespace ThreeSum.ReportingHostPrefixOrder
theorem _root_.solution {h J k i : ℕ} (hk : k ≤ J) (hi : i < (prefixes h k).length) :
    (preR h J k i).card = k*h := by rw [preR_get hi]; exact rightSet_card hk _
end ThreeSum.ReportingHostPrefixOrder
