-- Prove2me | solution 1 for ThreeSum.SharedReportingBankSources.entry_reuse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:23:25.66686+00:00
-- url     : https://prove2.me/submissions/4491d5f0-8f6e-4d73-8649-8484999461fb

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
import Theorems.Thm_ThreeSum_SharedReportingBankSources_tables_reuse

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light GlobalEncoding BlockEncoding BlockIndexedQuery SharedReportingBankData
open BlockSourceOccurrenceOrder BlockSourceSharing OutputDecodeRecords
namespace ThreeSum.SharedReportingBankSources
theorem _root_.solution {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k record : ℕ} {μ : ℕ → ℤ}
    {D : ReportingHostLevelData.Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    {q q' : GlobalOutput h J} (ho : outputOccurrences q=outputOccurrences q')
    (H : Entry μ record D hk (leftSource p B b q) (rightSource p shift C c q)) :
    Entry μ record D hk (leftSource p B b q') (rightSource p shift C c q') :=
  ⟨H.header,tables_reuse p shift B C b c ho H.tables⟩
end ThreeSum.SharedReportingBankSources
