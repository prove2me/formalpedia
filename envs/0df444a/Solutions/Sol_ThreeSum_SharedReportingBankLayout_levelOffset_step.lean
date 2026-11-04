-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLayout.levelOffset_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:08:03.712028+00:00
-- url     : https://prove2.me/submissions/a973bf08-6c56-4ed1-a323-155777ed3707

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLayout
open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000
namespace ThreeSum.SharedReportingBankLayout
theorem _root_.solution (h J : ℕ) (boxCut : ℕ → ℕ) (k : ℕ) :
    levelOffset h J boxCut k ≤ levelOffset h J boxCut (k+1) := by
  rw [levelOffset]
  omega
end ThreeSum.SharedReportingBankLayout
