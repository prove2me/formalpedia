-- Prove2me | solution 1 for ThreeSum.SourceBandBankLayout.work_le_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:23:24.966863+00:00
-- url     : https://prove2.me/submissions/7ca3a1f1-a4a7-498a-9492-33adf6035e8b

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
import Theorems.Thm_ThreeSum_SourceBandBankLayout_complete_end

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankLayout
open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder
namespace ThreeSum.SourceBandBankLayout
theorem _root_.solution (base h J cut i : ℕ) :
    work (baseAt base h J cut i) (LightBlockSourceCatalog.count h J) (J*(512*h)) cut ≤
      baseAt base h J cut (i+1) := by
  rw [← complete_end]
  exact (Nat.le_add_right _ _).trans (le_max_left _ _)
end ThreeSum.SourceBandBankLayout
