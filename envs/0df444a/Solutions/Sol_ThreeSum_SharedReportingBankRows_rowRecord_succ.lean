-- Prove2me | solution 1 for ThreeSum.SharedReportingBankRows.rowRecord_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:47:52.227996+00:00
-- url     : https://prove2.me/submissions/38970dc6-492c-4d59-9ba6-23a55e05799f

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
theorem _root_.solution (record K q : ℕ) : rowRecord record K (q+1)=rowRecord record K q+5*K := by
  unfold rowRecord
  ring
end ThreeSum.SharedReportingBankRows
