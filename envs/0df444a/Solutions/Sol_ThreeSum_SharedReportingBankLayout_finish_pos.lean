-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLayout.finish_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:20:40.366263+00:00
-- url     : https://prove2.me/submissions/ef28e2e6-fda3-4cba-abf7-e5633907524e

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
import Theorems.Thm_ThreeSum_SharedReportingBankLayout_ordered

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLayout
open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000
namespace ThreeSum.SharedReportingBankLayout
theorem _root_.solution (base h J k boxCut : ℕ) : base < finish base h J k boxCut := by
  have hh := ordered base h J k boxCut
  unfold finish
  omega
end ThreeSum.SharedReportingBankLayout
