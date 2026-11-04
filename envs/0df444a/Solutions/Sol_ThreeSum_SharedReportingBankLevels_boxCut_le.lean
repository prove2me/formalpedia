-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLevels.boxCut_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:27:10.866742+00:00
-- url     : https://prove2.me/submissions/d527f3d8-165b-42e5-ad65-5039efb33d35

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000
namespace ThreeSum.SharedReportingBankLevels
theorem _root_.solution (h J k : ℕ) : boxCut h J k ≤ residual h J k := Nat.sub_le _ _
end ThreeSum.SharedReportingBankLevels
