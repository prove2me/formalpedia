-- Prove2me | solution 1 for ThreeSum.LightSharedReportingCell.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:20:27.205399+00:00
-- url     : https://prove2.me/submissions/02ca87ce-e62d-4566-92b6-fc4ea2d5de23

import Definitions.Def_Submission_ThreeSum_LightSharedReportingEntry
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
import Definitions.Def_Submission_ThreeSum_LightSharedReportingCell

set_option autoImplicit false
open ThreeSum ThreeSum.LightSharedReportingCell
open Light SubsetAddress LightPascal ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog SharedReportingBankData
open SharedReportingBankLayout
set_option maxHeartbeats 2900000
set_option maxRecDepth 15000
namespace ThreeSum.LightSharedReportingCell
theorem _root_.solution : program.length=63 := rfl
end ThreeSum.LightSharedReportingCell
