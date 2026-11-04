-- Prove2me | solution 1 for ThreeSum.SharedReportingBankRows.rank_next_c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:54:41.82194+00:00
-- url     : https://prove2.me/submissions/4ab04f34-770a-4106-b18c-338910e288a1

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankRows
open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1800000
namespace ThreeSum.SharedReportingBankRows
theorem _root_.solution (nb nc s i j : ℕ) : rank nb nc s i (j+1)=rank nb nc s i j+1 := by
  unfold rank
  omega
end ThreeSum.SharedReportingBankRows
