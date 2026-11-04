-- Prove2me | solution 1 for ThreeSum.SharedReportingBankRows.rowBase_next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:27:37.943444+00:00
-- url     : https://prove2.me/submissions/c6f12fe5-4733-4df4-80a0-009ecd70e2fb

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
theorem _root_.solution (base h J K q : ℕ) :
    baseAt (rowBase base h J K q) h J K=rowBase base h J K (q+1) := by
  unfold rowBase baseAt
  ring
end ThreeSum.SharedReportingBankRows
