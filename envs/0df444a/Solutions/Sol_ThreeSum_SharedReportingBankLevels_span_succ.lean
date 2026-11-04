-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLevels.span_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:27:44.712024+00:00
-- url     : https://prove2.me/submissions/181ab09c-40cb-4573-9a65-54ae4c29d63d

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000
namespace ThreeSum.SharedReportingBankLevels
theorem _root_.solution (h k : ℕ) : prefixSpan h (k+1)=prefixSpan h k+1+count h (k+1) := by
  unfold prefixSpan
  rw [LightRadixKeys.offset]
  change LightRadixKeys.offset (localPairs h) k+1+count h k+1+count h (k+1)=_
  omega
end ThreeSum.SharedReportingBankLevels
