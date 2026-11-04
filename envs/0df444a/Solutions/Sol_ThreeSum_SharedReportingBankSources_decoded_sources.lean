-- Prove2me | solution 1 for ThreeSum.SharedReportingBankSources.decoded_sources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:13:16.462195+00:00
-- url     : https://prove2.me/submissions/45f67ef0-d19e-490a-9196-cd913685647b

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
import Theorems.Thm_ThreeSum_LightBlockSourceCatalog_Stored_decoded
import Theorems.Thm_ThreeSum_SourceBandBankData_Stored_decoded
import Theorems.Thm_ThreeSum_SourceBandBankLayout_At_decoded


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light GlobalEncoding BlockEncoding BlockIndexedQuery SharedReportingBankData
open BlockSourceOccurrenceOrder BlockSourceSharing OutputDecodeRecords
namespace ThreeSum.SharedReportingBankSources
theorem _root_.solution {μ : ℕ → ℤ} {fB fC : ℕ → ℤ}
    {base NB NC g h J occ i j k : ℕ} {p shift : ℤ}
    (H : SourceBandBankData.Stored μ fB fC base NB NC g h J (2*h*J) occ p shift)
    (hi : i < SourceBandPairSlices.count NB NC g) (hj : j < SourceBandPairSlices.count NB NC g)
    (hk : k < localCount h^J) :
    ReportingHostLevelData.Sources μ p shift
      (SourceBandPartition.source NB g i) (SourceBandPartition.source NC g j)
      (fun t : Fin NB => fB t.val) (fun t : Fin NC => fC t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J))
      (leftBase base h J (2*h*J) i (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k))
      (rightBase base h J (2*h*J) j (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k)) :=
  ⟨(H.decoded hi hk).left,(H.decoded hj hk).right⟩
end ThreeSum.SharedReportingBankSources
