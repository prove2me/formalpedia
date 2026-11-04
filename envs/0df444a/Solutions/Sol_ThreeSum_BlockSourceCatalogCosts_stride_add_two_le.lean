-- Prove2me | solution 1 for ThreeSum.BlockSourceCatalogCosts.stride_add_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:04:23.137284+00:00
-- url     : https://prove2.me/submissions/5cb8bf43-36c5-47c2-8176-269ca8eea9f8

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalogProgram
import Definitions.Def_Submission_ThreeSum_BlockSourceStageCosts
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts

set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceCatalogCosts
open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout
namespace ThreeSum.BlockSourceCatalogCosts
theorem _root_.solution (W cut : ℕ) :
    stride W cut+2 ≤ (2*W+7)*(downsetCap W cut+1) := by
  unfold stride family
  nlinarith
end ThreeSum.BlockSourceCatalogCosts
