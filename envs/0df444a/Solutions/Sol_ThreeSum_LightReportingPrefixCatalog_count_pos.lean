-- Prove2me | solution 1 for ThreeSum.LightReportingPrefixCatalog.count_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:04:40.930526+00:00
-- url     : https://prove2.me/submissions/89f736f6-0a7d-44bf-9ef7-3f06ba2d319f

import Definitions.Def_Submission_ThreeSum_LightReportingPrefixArrays
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalogSetup
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingPrefixCatalog
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPrefixCatalog ReportingHostPrefixOrder ReportingHostSuffix
open LightReportingSuffixCatalog
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits}
namespace ThreeSum.LightReportingPrefixCatalog
theorem _root_.solution (h k : ℕ) : 0 < count h k := by
  exact Nat.pow_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))
end ThreeSum.LightReportingPrefixCatalog
