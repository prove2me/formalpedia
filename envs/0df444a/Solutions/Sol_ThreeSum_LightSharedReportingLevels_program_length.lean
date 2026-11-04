-- Prove2me | solution 1 for ThreeSum.LightSharedReportingLevels.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:41:08.515679+00:00
-- url     : https://prove2.me/submissions/cd9055f7-5758-4b4e-931c-4de8de11defa

import Definitions.Def_Submission_ThreeSum_LightSharedReportingCell
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Definitions.Def_Submission_ThreeSum_LightSharedReportingLoop
import Definitions.Def_Submission_ThreeSum_LightSharedReportingLevels

set_option autoImplicit false
open ThreeSum ThreeSum.LightSharedReportingLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData SharedReportingBankLevels
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000
namespace ThreeSum.LightSharedReportingLevels
theorem _root_.solution : program.length=65 := rfl
end ThreeSum.LightSharedReportingLevels
