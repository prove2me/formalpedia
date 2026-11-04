-- Prove2me | solution 1 for ThreeSum.SourceBandBankLayout.At.of_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:31:15.454363+00:00
-- url     : https://prove2.me/submissions/4dea9e3d-2389-4e34-bd99-6012afc5d9e9

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
import Theorems.Thm_ThreeSum_SourceBandBankLayout_work_le_end
import Definitions.Def_WeightedCache3SUM_Alias_b45ecd123880fb3a

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankLayout
open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder
namespace ThreeSum.SourceBandBankLayout
namespace At
theorem _root_.solution {μ ν : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut i bound : ℕ}
    {p shift : ℤ} (H : At μ fL fR base NL NR g h J cut p shift i)
    (K : Kept μ ν bound) (hb : baseAt base h J cut (i+1) ≤ bound) :
    At ν fL fR base NL NR g h J cut p shift i := by
  intro k hk
  exact bank_of_kept (H k hk) hk K ((work_le_end base h J cut i).trans hb)
end At
end ThreeSum.SourceBandBankLayout
