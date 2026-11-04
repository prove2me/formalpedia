-- Prove2me | solution 1 for ThreeSum.SharedReportingBankRows.rank_next_s
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:41:34.396248+00:00
-- url     : https://prove2.me/submissions/913b6eeb-3fa5-4ced-87f5-01a255da6c46

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
theorem _root_.solution {nb nc s i j : ℕ} (hi : i+1=nb) (hj : j+1=nc) :
    rank nb nc (s+1) 0 0=rank nb nc s i j+1 := by
  subst nb nc
  unfold rank
  ring
end ThreeSum.SharedReportingBankRows
