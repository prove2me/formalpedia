-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFastProgramResources.color_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:28:14.3278+00:00
-- url     : https://prove2.me/submissions/f20231b3-a5ce-4dc5-b29b-c47429a1ab6f

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_Submission_ThreeSum_ThreeSumColorDriverResources
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
import Theorems.Thm_ThreeSum_WeightedGlobalFastProgramResources_scan_ok
import Theorems.Thm_ThreeSum_ThreeSumColorDriverResources_color_of_ok


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFastProgramResources
open Light LightWeightedGlobalFastProgram LightWeightedGlobalFastProgramProof
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedGlobalFastProgramResources
theorem _root_.solution {M b p K κ n U free depth dd : ℕ} {colorNeed : ℕ→ℕ→Need} {lim : Limits}
    (H : (need M b p K κ colorNeed n U).Ok lim free depth)
    (hd : dd+(colorNeed n U).depth≤lim.depth) :
    (colorNeed n U).Ok lim (scanFree M b p K κ n free+6) dd :=
  ThreeSumColorDriverResources.color_of_ok (scan_ok H) hd
end ThreeSum.WeightedGlobalFastProgramResources
