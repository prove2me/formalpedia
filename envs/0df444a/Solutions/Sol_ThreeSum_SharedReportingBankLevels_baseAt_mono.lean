-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLevels.baseAt_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:23:39.776476+00:00
-- url     : https://prove2.me/submissions/d8bd286f-dd1c-4399-a8da-e4969a20130e

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Theorems.Thm_ThreeSum_SharedReportingBankLayout_levelOffset_mono


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000
namespace ThreeSum.SharedReportingBankLevels
theorem _root_.solution (base h J : ℕ) : Monotone (baseAt base h J) := by
  intro i j hij
  exact Nat.add_le_add_left (levelOffset_mono h J (boxCut h J) hij) base
end ThreeSum.SharedReportingBankLevels
