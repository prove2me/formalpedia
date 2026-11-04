-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLevels.Built.append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:11:05.837125+00:00
-- url     : https://prove2.me/submissions/e5096f95-01fe-4ff7-9bcd-3e9d8bd0e252

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_baseAt_mono
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_catalog_low
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_catalog_end
import Theorems.Thm_ThreeSum_SharedReportingBankData_Entry_of_later


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000
namespace ThreeSum.SharedReportingBankLevels
namespace Built
theorem _root_.solution {μ ν : ℕ → ℤ} {record base h J i : ℕ}
    {f g : Finset (Fin (J*(512*h))) → ℤ} (H : Built μ record base h J i f g)
    (hi : i ≤ J)
    (Hnew : Entry ν (record+5*i) (catalogAt base h J i) hi f g)
    (hkeep : KeptBut μ ν (baseAt base h J i) (record+5*i) 5)
    (hrecord : record+5*i+5 ≤ base) : Built ν record base h J (i+1) f g := by
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · obtain ⟨hjJ,Hj⟩ := H j hj
    have hlow := catalog_low base h J j
    have hend := catalog_end base h J j
    have hbefore := baseAt_mono base h J (show j+1 ≤ i by omega)
    refine ⟨hjJ,Hj.of_later hkeep (by omega) hrecord
      (Nat.le_add_right _ _) hlow.1 hlow.2.1 hlow.2.2
      (hend.1.trans hbefore) (hend.2.1.trans hbefore) (hend.2.2.trans hbefore)⟩
  · exact ⟨hi,Hnew⟩
end Built
end ThreeSum.SharedReportingBankLevels
