-- Prove2me | solution 1 for ThreeSum.ReportingHostPackedCatalog.pairKey_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:08:31.520863+00:00
-- url     : https://prove2.me/submissions/b0187f57-9a89-4fda-a79d-add67f9e9903

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPackedCatalog
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder
set_option maxHeartbeats 600000
namespace ThreeSum.ReportingHostPackedCatalog
theorem _root_.solution {radix left right : ℕ} (hl : left < radix) (hr : right < radix) :
    pairKey radix left right < radix^2 := by unfold pairKey; nlinarith
end ThreeSum.ReportingHostPackedCatalog
