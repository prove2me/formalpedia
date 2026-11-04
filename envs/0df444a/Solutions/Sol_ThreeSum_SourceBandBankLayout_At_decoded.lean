-- Prove2me | solution 1 for ThreeSum.SourceBandBankLayout.At.decoded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:15:53.766725+00:00
-- url     : https://prove2.me/submissions/c498ab94-38bf-4c75-a5b7-e8f172c25d87

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
import Theorems.Thm_ThreeSum_LightBlockSourceCatalog_Stored_decoded


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankLayout
open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder
namespace ThreeSum.SourceBandBankLayout
namespace At
theorem _root_.solution {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut i k : ℕ}
    {p shift : ℤ} (H : At μ fL fR base NL NR g h J cut p shift i)
    (hk : k < OutputDecodeRecords.localCount h^J) :
    LightBlockSourceBatch.BankAt μ (baseAt base h J cut i) (LightBlockSourceCatalog.count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (OutputDecodeRecords.layerCount h) J k)
      p shift (SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
      (SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (OutputDecodeRecords.outputDefault h J)) :=
  LightBlockSourceCatalog.Stored.decoded H hk
end At
end ThreeSum.SourceBandBankLayout
