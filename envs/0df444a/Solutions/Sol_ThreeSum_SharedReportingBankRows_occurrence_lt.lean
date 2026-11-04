-- Prove2me | solution 1 for ThreeSum.SharedReportingBankRows.occurrence_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:40:00.166354+00:00
-- url     : https://prove2.me/submissions/76348aae-ed52-446c-b858-edfbfbabed9c

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
theorem _root_.solution {S nb nc s i j : ℕ}
    (he : rank nb nc s i j < pairs S nb nc) : s < S := by
  by_contra h
  have hs : S ≤ s := by omega
  have hp : S*nb ≤ s*nb+i := (Nat.mul_le_mul_right nb hs).trans (Nat.le_add_right _ _)
  have hq : S*nb*nc ≤ (s*nb+i)*nc+j :=
    (Nat.mul_le_mul_right nc hp).trans (Nat.le_add_right _ _)
  exact (not_lt_of_ge hq) he
end ThreeSum.SharedReportingBankRows
