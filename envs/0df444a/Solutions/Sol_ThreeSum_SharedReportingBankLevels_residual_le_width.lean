-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLevels.residual_le_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:38:09.993604+00:00
-- url     : https://prove2.me/submissions/4c6bc213-7590-421d-a189-087ff52dbf41

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000
namespace ThreeSum.SharedReportingBankLevels
theorem _root_.solution (h J k : ℕ) : residual h J k ≤ (J-k)*(512*h) := by
  unfold residual
  nlinarith
end ThreeSum.SharedReportingBankLevels
