-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixOrder.preL_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:06:40.276199+00:00
-- url     : https://prove2.me/submissions/777c79c1-eb8f-4d22-91a7-eec5b91b0eb0

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_preL_get
import Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_leftSet_card


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixOrder
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPairEnumeration
open ReportingHostPrefixMasks ReportingHostPairSegments
set_option maxHeartbeats 600000
namespace ThreeSum.ReportingHostPrefixOrder
theorem _root_.solution {h J k i : ℕ} (hk : k ≤ J) (hi : i < (prefixes h k).length) :
    (preL h J k i).card = k*h := by rw [preL_get hi]; exact leftSet_card hk _
end ThreeSum.ReportingHostPrefixOrder
