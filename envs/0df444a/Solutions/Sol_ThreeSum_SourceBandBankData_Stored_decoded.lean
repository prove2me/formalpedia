-- Prove2me | solution 1 for ThreeSum.SourceBandBankData.Stored.decoded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:26:31.866199+00:00
-- url     : https://prove2.me/submissions/6c24b241-739b-42af-bf6f-06cde6d914c7

import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Theorems.Thm_ThreeSum_LightBlockSourceCatalog_Stored_decoded
import Theorems.Thm_ThreeSum_SourceBandBankLayout_At_decoded


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankData
open Light GlobalEncoding SourceBandBankLayout OutputDecodeRecords
namespace ThreeSum.SourceBandBankData
namespace Stored
theorem _root_.solution {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut occ i k : ℕ} {p shift : ℤ}
    (H : Stored μ fL fR base NL NR g h J cut occ p shift)
    (hi : i < SourceBandPairSlices.count NL NR g) (hk : k < localCount h^J) :
    LightBlockSourceBatch.BankAt μ (baseAt (first base) h J cut i) (LightBlockSourceCatalog.count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k)
      p shift (SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
      (SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J)) :=
  (H.banks i hi).decoded hk
end Stored
end ThreeSum.SourceBandBankData
