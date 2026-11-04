-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLevels.baseAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:39:49.107175+00:00
-- url     : https://prove2.me/submissions/5ac1b779-e427-4244-bb1b-0be5876ddfda

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000
namespace ThreeSum.SharedReportingBankLevels
theorem _root_.solution (base h J : ℕ) : baseAt base h J 0=base := rfl
end ThreeSum.SharedReportingBankLevels
