-- Prove2me | solution 1 for ThreeSum.SharedReportingBankHeader.levels_of_after
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:12:39.162466+00:00
-- url     : https://prove2.me/submissions/48a3ebb2-3051-45ec-8bed-9600e89de922

import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankHeader
import Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_of_after
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_catalog_low
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankHeader
open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1900000
namespace ThreeSum.SharedReportingBankHeader
theorem _root_.solution {μ ν : ℕ → ℤ} {record base h J K low : ℕ}
    {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Built μ record base h J K f g) (heq : ∀ a, low ≤ a → ν a=μ a)
    (hrecord : low ≤ record) (hbase : low ≤ base) : Built ν record base h J K f g := by
  intro k hk
  obtain ⟨hkJ,Hk⟩ := H k hk
  have hlo := catalog_low base h J k
  refine ⟨hkJ,⟨?_,Hk.tables.of_after heq (hbase.trans hlo.1)
    (hbase.trans hlo.2.1) (hbase.trans hlo.2.2)⟩⟩
  intro i hi
  exact (heq _ (by omega)).trans (Hk.header i hi)
end ThreeSum.SharedReportingBankHeader
