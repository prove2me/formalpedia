-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLayout.cap_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:08:14.361541+00:00
-- url     : https://prove2.me/submissions/734f0539-351d-4988-b802-5d93a85d0815

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
    masks base h J k boxCut+cap h J k boxCut ≤ work base h J k boxCut := by
  unfold work
  omega
end ThreeSum.SharedReportingBankLayout
