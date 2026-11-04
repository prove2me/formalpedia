-- Prove2me | solution 1 for ThreeSum.SourceFiniteData.Stored.decoded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:56:01.884637+00:00
-- url     : https://prove2.me/submissions/206ac55e-4155-4d97-bebc-33af9263533d

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
import Definitions.Def_Submission_ThreeSum_SourceFiniteData
import Theorems.Thm_ThreeSum_LightBlockSourceCatalog_Stored_decoded
import Theorems.Thm_ThreeSum_SourceBandBankData_Stored_decoded
import Theorems.Thm_ThreeSum_SourceBandBankLayout_At_decoded
import Theorems.Thm_ThreeSum_SourceBandFinite_decoded


set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteData
open Light GlobalEncoding OutputDecodeRecords BandPartition BandCandidateRows BandRawA
namespace ThreeSum.SourceFiniteData
namespace Stored
theorem _root_.solution {μ : ℕ → ℤ} {base g p h J cut i k : ℕ} {B C : List ℤ} {shift r : ℤ}
    (H : Stored μ base g p h J cut B C shift r)
    (hi : i < SourceBandPairSlices.count B.length C.length g) (hk : k < localCount h^J) :
    LightBlockSourceBatch.BankAt μ
      (SourceBandBankLayout.baseAt
        (LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase base) B.length C.length g h J+5)
        h J cut i) (LightBlockSourceCatalog.count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k) (p : ℤ) shift
      (finiteBandPositions B.length g i) (fun t : Fin B.length => B.getD t.val 0)
      (finiteBandPositions C.length g i) (fun t : Fin C.length => C.getD t.val 0)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J)) :=
  SourceBandFinite.decoded H.banks hi hk
end Stored
end ThreeSum.SourceFiniteData
