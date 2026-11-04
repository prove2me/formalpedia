-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLevels.span_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:49:12.633353+00:00
-- url     : https://prove2.me/submissions/f6b655c7-7714-4d78-91ee-74f391049046

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_span_succ

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000
namespace ThreeSum.SharedReportingBankLevels
theorem _root_.solution (h : ℕ) : Monotone (prefixSpan h) :=
  monotone_nat_of_le_succ (fun k => by rw [span_succ]; omega)
end ThreeSum.SharedReportingBankLevels
