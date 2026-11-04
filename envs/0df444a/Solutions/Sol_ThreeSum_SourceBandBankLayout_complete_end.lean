-- Prove2me | solution 1 for ThreeSum.SourceBandBankLayout.complete_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:17:13.101194+00:00
-- url     : https://prove2.me/submissions/54014072-8cd4-40b0-a208-3769e4e7b20d

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
import Theorems.Thm_ThreeSum_SourceBandBankLayout_work_add
import Theorems.Thm_ThreeSum_SourceBandBankLayout_host_space_add

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankLayout
open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder
namespace ThreeSum.SourceBandBankLayout
theorem _root_.solution (base h J cut i : ℕ) :
    LightBlockSourceRetainedHost.space
      (work (baseAt base h J cut i) (LightBlockSourceCatalog.count h J) (J*(512*h)) cut) h J=
      baseAt base h J cut (i+1) := by
  rw [work_add,host_space_add]
  unfold baseAt span
  ring
end ThreeSum.SourceBandBankLayout
