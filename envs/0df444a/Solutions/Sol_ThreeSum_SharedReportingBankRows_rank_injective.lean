-- Prove2me | solution 1 for ThreeSum.SharedReportingBankRows.rank_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:55:59.998091+00:00
-- url     : https://prove2.me/submissions/09939cd8-50ee-4820-a8a4-c58c2ab92653

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Theorems.Thm_ThreeSum_SharedReportingBankRows_digit_injective

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankRows
open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1800000
namespace ThreeSum.SharedReportingBankRows
theorem _root_.solution {nb nc s i j s' i' j' : ℕ}
    (hi : i < nb) (hj : j < nc) (hi' : i' < nb) (hj' : j' < nc)
    (he : rank nb nc s i j=rank nb nc s' i' j') : s=s' ∧ i=i' ∧ j=j' := by
  have hinner := digit_injective hj hj' he
  have houter := digit_injective hi hi' hinner.1
  exact ⟨houter.1,houter.2,hinner.2⟩
end ThreeSum.SharedReportingBankRows
