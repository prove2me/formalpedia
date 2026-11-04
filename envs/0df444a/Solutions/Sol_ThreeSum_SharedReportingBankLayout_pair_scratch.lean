-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLayout.pair_scratch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:07:33.397278+00:00
-- url     : https://prove2.me/submissions/e86ef3df-c5af-44f8-99f6-5150baf862a2

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLayout
open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000
namespace ThreeSum.SharedReportingBankLayout
theorem _root_.solution (base h J k boxCut : ℕ) :
    work base h J k boxCut+2*(512*h)+2 ≤ finish base h J k boxCut := by
  unfold finish localWidth
  omega
end ThreeSum.SharedReportingBankLayout
