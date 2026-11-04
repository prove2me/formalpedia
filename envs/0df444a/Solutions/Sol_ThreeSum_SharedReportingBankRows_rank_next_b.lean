-- Prove2me | solution 1 for ThreeSum.SharedReportingBankRows.rank_next_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:50:51.913584+00:00
-- url     : https://prove2.me/submissions/a825b93c-3386-4c70-bb7b-8226d6692df7

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
theorem _root_.solution {nb nc s i j : ℕ} (hj : j+1=nc) :
    rank nb nc s (i+1) 0=rank nb nc s i j+1 := by
  subst nc
  unfold rank
  ring
end ThreeSum.SharedReportingBankRows
