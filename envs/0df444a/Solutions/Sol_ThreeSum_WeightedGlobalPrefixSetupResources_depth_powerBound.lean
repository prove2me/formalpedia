-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPrefixSetupResources.depth_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:11:14.536782+00:00
-- url     : https://prove2.me/submissions/e593ae5b-d018-4f2e-907f-a9a3603b67fc

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_FrontendResources
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSetupResources
import Theorems.Thm_ThreeSum_WeightedGlobalPrefixSetupResources_dimensions_powerBound
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrefixSetupResources
open Light LightWeightedGlobalPrefixSetup StageBounds WeightedGlobalCoverScale
open WeightedGlobalFrontendResources
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
namespace ThreeSum.WeightedGlobalPrefixSetupResources
theorem _root_.solution {m : ℕ} (hm : 0<m) (F : ℕ) :
    PowerBound (fun n=>(need m (radixLength m n) F).depth) 0 := by
  exact (dimensions_powerBound hm).add_same (PowerBound.const 4)
end ThreeSum.WeightedGlobalPrefixSetupResources
