-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLayout.stageR_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:07:50.129394+00:00
-- url     : https://prove2.me/submissions/c4d2a709-6bff-4258-968e-88f24a1a8fbb

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLayout
open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000
namespace ThreeSum.SharedReportingBankLayout
theorem _root_.solution (base h k : ℕ) :
    stageR base h k=LightRadixKeys.space (stageL base h) (localPairs h) k := by
  unfold stageR prefixSpan LightRadixKeys.space count localPairs localWidth
  omega
end ThreeSum.SharedReportingBankLayout
