-- Prove2me | solution 1 for ThreeSum.SharedReportingBankHeader.levels_of_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:52:57.59963+00:00
-- url     : https://prove2.me/submissions/adaf932e-f18e-4391-8f26-976434838e49

import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankHeader
import Theorems.Thm_Light_Seg_of_kept
import Theorems.Thm_ThreeSum_BandRawA_Stored_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_00da40658bb1c003
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Definitions.Def_WeightedCache3SUM_Alias_82db098e10427a83
import Theorems.Thm_ThreeSum_ReportingHostLevelData_Sources_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_ed168a32962ea724
import Theorems.Thm_ThreeSum_SharedReportingBankData_Entry_of_kept
import Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_of_kept
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_baseAt_mono
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_catalog_end
import Definitions.Def_WeightedCache3SUM_Alias_470e48753c64c7fc
import Theorems.Thm_ThreeSum_SourceBandBankLayout_At_of_kept
import Theorems.Thm_ThreeSum_SourceBandBankLayout_baseAt_mono
import Theorems.Thm_ThreeSum_SourceBandData_At_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_78e5c19e1b3827d6


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankHeader
open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1900000
namespace ThreeSum.SharedReportingBankHeader
theorem _root_.solution {μ ν : ℕ → ℤ} {record base h J K bound : ℕ}
    {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Built μ record base h J K f g) (heq : Kept μ ν bound)
    (hrecord : record+5*K ≤ bound) (hbase : baseAt base h J K ≤ bound) :
    Built ν record base h J K f g := by
  intro k hk
  obtain ⟨hkJ,Hk⟩ := H k hk
  have hend := catalog_end base h J k
  have hbefore := (baseAt_mono base h J (show k+1 ≤ K by omega)).trans hbase
  refine ⟨hkJ,Hk.of_kept heq (by omega) (hend.1.trans hbefore)
    (hend.2.1.trans hbefore) (hend.2.2.trans hbefore)⟩
end ThreeSum.SharedReportingBankHeader
