-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLevels.finish_baseAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:27:25.836542+00:00
-- url     : https://prove2.me/submissions/0397b180-a88c-4976-884f-d828aa9ee2df

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Theorems.Thm_ThreeSum_SharedReportingBankLayout_finish_level


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000
namespace ThreeSum.SharedReportingBankLevels
theorem _root_.solution (base h J k : ℕ) :
    finish (baseAt base h J k) h J k (boxCut h J k)=baseAt base h J (k+1) :=
  finish_level base h J k (boxCut h J)
end ThreeSum.SharedReportingBankLevels
