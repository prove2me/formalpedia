-- Prove2me | solution 1 for ThreeSum.SharedReportingBankHeader.Stored.row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:54:36.168366+00:00
-- url     : https://prove2.me/submissions/a08d10c2-d44c-4597-bcb7-f805c6c265c5

import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankHeader
import Theorems.Thm_ThreeSum_SharedReportingBankRows_rank_lt


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankHeader
open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1900000
namespace ThreeSum.SharedReportingBankHeader
namespace Stored
theorem _root_.solution {μ : ℕ → ℤ} {free h J NB NC g s i j : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : Stored μ free h J NB NC g fB fC p shift)
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) :
    Built μ (rowRecord (records free) (levels J) (rank (BandPartition.size NB g) (BandPartition.size NC g) s i j))
      (rowBase (payload free h J NB NC g) h J (levels J) (rank (BandPartition.size NB g) (BandPartition.size NC g) s i j))
      h J (levels J)
      (BlockIndexedQuery.leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val)
        (BlockSourceOccurrenceOrder.representative h J s))
      (BlockIndexedQuery.rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val)
        (BlockSourceOccurrenceOrder.representative h J s)) :=
  H.rows s hs i hi j hj (rank_lt hs hi hj)
end Stored
end ThreeSum.SharedReportingBankHeader
