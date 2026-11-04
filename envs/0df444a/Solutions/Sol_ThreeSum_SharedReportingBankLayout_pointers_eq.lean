-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLayout.pointers_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:07:51.40949+00:00
-- url     : https://prove2.me/submissions/786b0103-98fb-4cc7-8ddd-e669df529523

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
    pointers base h k=LightRadixKeys.space (stageR base h k) (localPairs h) k := by
  unfold pointers prefixSpan LightRadixKeys.space count localPairs localWidth
  omega
end ThreeSum.SharedReportingBankLayout
