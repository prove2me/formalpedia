-- Prove2me | solution 1 for ThreeSum.SharedReportingBankRows.levels_of_later_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:06:50.469768+00:00
-- url     : https://prove2.me/submissions/f72a4305-73b3-4961-a109-8d5200e47679

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Theorems.Thm_ThreeSum_SharedReportingBankRows_entry_of_later_block
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_baseAt_mono
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_catalog_end
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_catalog_low
import Theorems.Thm_ThreeSum_SourceBandBankLayout_baseAt_mono


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankRows
open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1800000
namespace ThreeSum.SharedReportingBankRows
theorem _root_.solution {μ ν : ℕ → ℤ} {record base h J K nextRecord nextBase : ℕ}
    {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Built μ record base h J K f g)
    (heq : KeptBut μ ν nextBase nextRecord (5*K))
    (hrecords : record+5*K ≤ nextRecord) (hnext : nextRecord+5*K ≤ base)
    (hpayload : baseAt base h J K ≤ nextBase) : Built ν record base h J K f g := by
  intro k hk
  obtain ⟨hkJ,Hk⟩ := H k hk
  have hlow := catalog_low base h J k
  have hend := catalog_end base h J k
  have hbefore := (baseAt_mono base h J (show k+1 ≤ K by omega)).trans hpayload
  refine ⟨hkJ,entry_of_later_block Hk heq (by omega) hnext
    ((Nat.le_add_right _ _).trans hpayload) hlow.1 hlow.2.1 hlow.2.2
    (hend.1.trans hbefore) (hend.2.1.trans hbefore) (hend.2.2.trans hbefore)⟩
end ThreeSum.SharedReportingBankRows
