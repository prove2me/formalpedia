-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLayout.finish_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:16:07.80068+00:00
-- url     : https://prove2.me/submissions/2cdcb6c1-b850-49ee-9b9a-e968b0465d6b

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
import Theorems.Thm_ThreeSum_SharedReportingBankLayout_finish_add

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLayout
open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000
namespace ThreeSum.SharedReportingBankLayout
theorem _root_.solution (base h J k : ℕ) (boxCut : ℕ → ℕ) :
    finish (base+levelOffset h J boxCut k) h J k (boxCut k)=
      base+levelOffset h J boxCut (k+1) := by
  rw [finish_add,levelOffset]
  omega
end ThreeSum.SharedReportingBankLayout
