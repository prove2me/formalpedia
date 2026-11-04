-- Prove2me | solution 1 for ThreeSum.SharedReportingBankRows.rowBase_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:28:34.267256+00:00
-- url     : https://prove2.me/submissions/8d444291-e191-4401-849e-c64ab0cd7bd0

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
theorem _root_.solution (base h J K : ℕ) : Monotone (rowBase base h J K) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _
end ThreeSum.SharedReportingBankRows
