-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLayout.table_scratch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:07:48.900205+00:00
-- url     : https://prove2.me/submissions/429c251e-571f-49c9-8701-e7de49886b0e

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
    work base h J k boxCut+1+tableSize (J*(512*h))+(J*(512*h)+1) ≤
      finish base h J k boxCut := by
  unfold finish width localWidth
  omega
end ThreeSum.SharedReportingBankLayout
