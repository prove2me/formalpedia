-- Prove2me | solution 1 for ThreeSum.ReportingHostPackedCatalog.packed_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:06:28.986282+00:00
-- url     : https://prove2.me/submissions/840e6ec2-3157-4bb5-abf1-1861f8e175f6

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPackedCatalog
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder
set_option maxHeartbeats 600000
namespace ThreeSum.ReportingHostPackedCatalog
theorem _root_.solution {key : ℕ → ℕ} {n i U : ℕ} (hi : i < n) (hk : key i < U) :
    packed key n i < U*(n+1) := by unfold packed; nlinarith
end ThreeSum.ReportingHostPackedCatalog
