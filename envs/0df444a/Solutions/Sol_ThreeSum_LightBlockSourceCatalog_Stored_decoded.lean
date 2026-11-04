-- Prove2me | solution 1 for ThreeSum.LightBlockSourceCatalog.Stored.decoded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:02.685859+00:00
-- url     : https://prove2.me/submissions/b133fa64-e4df-47d7-ba30-8d75932c9fb1

import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatch
import Definitions.Def_Submission_ThreeSum_LightSourceOccurrenceArray
import Definitions.Def_Submission_ThreeSum_BlockSourceOccurrenceOrder
import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Theorems.Thm_ThreeSum_BlockSourceOccurrenceOrder_decoded_occurrences
import Theorems.Thm_ThreeSum_LightBlockSourceBatch_BankAt_reuse
import Theorems.Thm_ThreeSum_OutputDecodeOccurrenceCode_source_code_lt


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceCatalog
open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding LightBlockSourceBatchLayout
open BlockSourceOccurrenceOrder OutputDecodeOrder OutputDecodeRecords
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
namespace ThreeSum.LightBlockSourceCatalog
namespace Stored
theorem _root_.solution {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {μ : ℕ → ℤ} {h J base cut k : ℕ} {P shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ}
    (H : Stored μ h J base cut P shift B b A a) (hk : k < localCount h^J) :
    LightBlockSourceBatch.BankAt μ base (count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k)
      P shift B b A a ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J)) :=
  (H _ (OutputDecodeOccurrenceCode.source_code_lt h J k)).reuse (decoded_occurrences hk)
end Stored
end ThreeSum.LightBlockSourceCatalog
