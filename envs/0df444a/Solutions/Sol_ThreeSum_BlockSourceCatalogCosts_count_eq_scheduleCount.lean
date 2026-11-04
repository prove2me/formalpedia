-- Prove2me | solution 1 for ThreeSum.BlockSourceCatalogCosts.count_eq_scheduleCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:57:52.000009+00:00
-- url     : https://prove2.me/submissions/d33d04b4-1f75-425f-a81e-ac49f0204639

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalogProgram
import Definitions.Def_Submission_ThreeSum_BlockSourceStageCosts
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Theorems.Thm_ThreeSum_BlockSourceSharing_occurrence_card
import Theorems.Thm_ThreeSum_BlockSourceSharing_occurrence_card_eq_scheduleCount


set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceCatalogCosts
open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout
namespace ThreeSum.BlockSourceCatalogCosts
theorem _root_.solution (n : ℕ) :
    LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)) =
      scheduleCount n := by
  unfold LightBlockSourceCatalog.count
  rw [← occurrence_card,occurrence_card_eq_scheduleCount]
end ThreeSum.BlockSourceCatalogCosts
