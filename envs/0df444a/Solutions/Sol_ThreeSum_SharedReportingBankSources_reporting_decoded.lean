-- Prove2me | solution 1 for ThreeSum.SharedReportingBankSources.reporting_decoded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:23:27.118784+00:00
-- url     : https://prove2.me/submissions/27dab2ae-9c78-437c-9c21-37783217c61e

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
import Theorems.Thm_ThreeSum_SharedReportingBankSources_tables_reuse
import Theorems.Thm_ThreeSum_BlockSourceOccurrenceOrder_decoded_occurrences
import Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_reporting


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light GlobalEncoding BlockEncoding BlockIndexedQuery SharedReportingBankData
open BlockSourceOccurrenceOrder BlockSourceSharing OutputDecodeRecords
namespace ThreeSum.SharedReportingBankSources
theorem _root_.solution {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k output record : ℕ} {μ : ℕ → ℤ}
    {D : ReportingHostLevelData.Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (houtput : output < localCount h^J)
    (H : Entry μ record D hk
      (leftSource p B b (representative h J
        (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output)))
      (rightSource p shift C c (representative h J
        (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output)))) :
    ReportingHostLevelData.Stored μ D hk p shift B C b c
      ((GlobalKeyEnumeration.globalRecords h J).getD output (outputDefault h J)) :=
  (tables_reuse p shift B C b c (decoded_occurrences houtput) H.tables).reporting p shift B C b c _
end ThreeSum.SharedReportingBankSources
