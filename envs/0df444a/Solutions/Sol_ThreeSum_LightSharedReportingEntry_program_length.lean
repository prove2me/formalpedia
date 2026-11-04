-- Prove2me | solution 1 for ThreeSum.LightSharedReportingEntry.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:06:42.549779+00:00
-- url     : https://prove2.me/submissions/c00d902c-6f18-4f73-bd07-d7c52020cd0f

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightSharedReportingEntry

set_option autoImplicit false
open ThreeSum ThreeSum.LightSharedReportingEntry
open Light SubsetAddress LightPascal ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
open SharedReportingBankData
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
namespace ThreeSum.LightSharedReportingEntry
theorem _root_.solution : program.length=53 := rfl
end ThreeSum.LightSharedReportingEntry
