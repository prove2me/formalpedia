-- Prove2me | solution 1 for ThreeSum.BlockSourceCatalogCosts.stageFamilyCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:54.098197+00:00
-- url     : https://prove2.me/submissions/46dfe3ff-6214-48a8-9486-2812ec47ede4

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalogProgram
import Definitions.Def_Submission_ThreeSum_BlockSourceStageCosts
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_count_eq_scheduleCount

set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceCatalogCosts
open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout
namespace ThreeSum.BlockSourceCatalogCosts
theorem _root_.solution (n : ℕ) : stageFamilyCount n = 2*bandCount n*scheduleCount n := by
  unfold stageFamilyCount
  rw [count_eq_scheduleCount]
end ThreeSum.BlockSourceCatalogCosts
