-- Prove2me | solution 1 for ThreeSum.SourceFiniteData.Stored.occurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:53:56.888627+00:00
-- url     : https://prove2.me/submissions/a7836b2d-c3d5-4a7c-b78e-ed5c7d7a2039

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
import Definitions.Def_Submission_ThreeSum_SourceFiniteData
import Theorems.Thm_ThreeSum_SourceBandFinite_occurrence


set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteData
open Light GlobalEncoding OutputDecodeRecords BandPartition BandCandidateRows BandRawA
namespace ThreeSum.SourceFiniteData
namespace Stored
theorem _root_.solution {μ : ℕ → ℤ} {base g p h J cut i k : ℕ} {B C : List ℤ} {shift r : ℤ}
    (H : Stored μ base g p h J cut B C shift r)
    (hi : i < SourceBandPairSlices.count B.length C.length g) (hk : k < LightBlockSourceCatalog.count h J) :
    LightBlockSourceBatch.BankAt μ
      (SourceBandBankLayout.baseAt
        (LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase base) B.length C.length g h J+5)
        h J cut i) (LightBlockSourceCatalog.count h J) cut k (p : ℤ) shift
      (finiteBandPositions B.length g i) (fun t : Fin B.length => B.getD t.val 0)
      (finiteBandPositions C.length g i) (fun t : Fin C.length => C.getD t.val 0)
      (BlockSourceOccurrenceOrder.representative h J k) :=
  SourceBandFinite.occurrence H.banks hi hk
end Stored
end ThreeSum.SourceFiniteData
