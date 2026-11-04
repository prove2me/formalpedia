-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFastProgramResources.scan_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:28:15.649821+00:00
-- url     : https://prove2.me/submissions/49651191-1e39-499b-bee1-e81c29f6f186

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_Submission_ThreeSum_ThreeSumColorDriverResources
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
import Theorems.Thm_ThreeSum_WeightedGlobalFastProgramResources_scan_ok
import Theorems.Thm_ThreeSum_ThreeSumColorDriverResources_scan_bounds_of_ok


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFastProgramResources
open Light LightWeightedGlobalFastProgram LightWeightedGlobalFastProgramProof
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedGlobalFastProgramResources
theorem _root_.solution {M b p K κ n U free depth : ℕ} {colorNeed : ℕ→ℕ→Need} {lim : Limits}
    (H : (need M b p K κ colorNeed n U).Ok lim free depth) :
    scanFree M b p K κ n free+6≤lim.space ∧
    (LightColorScanHost.word n : ℤ)≤lim.word ∧
    depth+ColorParameters.count (LightColorParametersCosts.width n)+(colorNeed n U).depth+5≤lim.depth := by
  have h := ThreeSumColorDriverResources.scan_bounds_of_ok (scan_ok H)
  exact ⟨h.1,h.2.1,by omega⟩
end ThreeSum.WeightedGlobalFastProgramResources
