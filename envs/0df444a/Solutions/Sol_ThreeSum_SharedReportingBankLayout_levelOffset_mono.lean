-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLayout.levelOffset_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:13:38.832843+00:00
-- url     : https://prove2.me/submissions/21c4cf32-8f54-47dc-886c-073f0f8f819a

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
import Theorems.Thm_ThreeSum_SharedReportingBankLayout_levelOffset_step

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLayout
open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000
namespace ThreeSum.SharedReportingBankLayout
theorem _root_.solution (h J : ℕ) (boxCut : ℕ → ℕ) : Monotone (levelOffset h J boxCut) :=
  monotone_nat_of_le_succ (levelOffset_step h J boxCut)
end ThreeSum.SharedReportingBankLayout
