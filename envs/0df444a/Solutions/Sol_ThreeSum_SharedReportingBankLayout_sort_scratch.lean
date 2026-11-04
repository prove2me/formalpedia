-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLayout.sort_scratch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:07:52.718403+00:00
-- url     : https://prove2.me/submissions/e9a4eeb0-2a05-4237-9069-0fd7f73ae39e

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
    work base h J k boxCut+count h k ≤ finish base h J k boxCut := by
  unfold finish
  omega
end ThreeSum.SharedReportingBankLayout
