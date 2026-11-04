-- Prove2me | solution 1 for ThreeSum.SharedReportingBankSources.tables_reuse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:12:34.993018+00:00
-- url     : https://prove2.me/submissions/49aa2e15-aaab-48bf-ac5e-7e98b7c975d5

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
import Theorems.Thm_ThreeSum_BlockSourceSharing_leftSource_eq_of_occurrences
import Theorems.Thm_ThreeSum_BlockSourceSharing_rightSource_eq_of_occurrences
import Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_leftSource_eq_of_occurrences
import Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_rightSource_eq_of_occurrences


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light GlobalEncoding BlockEncoding BlockIndexedQuery SharedReportingBankData
open BlockSourceOccurrenceOrder BlockSourceSharing OutputDecodeRecords
namespace ThreeSum.SharedReportingBankSources
theorem _root_.solution {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k : ℕ} {μ : ℕ → ℤ}
    {D : ReportingHostLevelData.Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    {q q' : GlobalOutput h J} (ho : outputOccurrences q=outputOccurrences q')
    (H : Tables μ D hk (leftSource p B b q) (rightSource p shift C c q)) :
    Tables μ D hk (leftSource p B b q') (rightSource p shift C c q') := by
  rw [← BlockSourceSharing.leftSource_eq_of_occurrences p B b ho,
    ← BlockSourceSharing.rightSource_eq_of_occurrences p shift C c ho]
  exact H
end ThreeSum.SharedReportingBankSources
