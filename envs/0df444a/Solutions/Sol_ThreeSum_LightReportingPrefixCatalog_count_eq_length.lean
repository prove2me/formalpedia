-- Prove2me | solution 1 for ThreeSum.LightReportingPrefixCatalog.count_eq_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:45.137444+00:00
-- url     : https://prove2.me/submissions/1b838e37-d257-4591-9884-1a8e16d8d8a0

import Definitions.Def_Submission_ThreeSum_LightReportingPrefixArrays
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalogSetup
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_prefixes_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingPrefixCatalog
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPrefixCatalog ReportingHostPrefixOrder ReportingHostSuffix
open LightReportingSuffixCatalog
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits}
namespace ThreeSum.LightReportingPrefixCatalog
theorem _root_.solution (h k : ℕ) : count h k = (prefixes h k).length :=
  (prefixes_length h k).symm
end ThreeSum.LightReportingPrefixCatalog
