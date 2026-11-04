-- Prove2me | solution 1 for ThreeSum.LightSwitchDepth.depth_eq_terminalDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:56:13.827695+00:00
-- url     : https://prove2.me/submissions/8b8971cc-e77a-44d3-b901-12bef9ba0fc2

import Definitions.Def_Submission_ThreeSum_LightSwitch
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth

set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchDepth
open Light
variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J d : ℕ}
namespace ThreeSum.LightSwitchDepth
theorem _root_.solution (n : ℕ) :
    depth (Scales.blockCount (Scales.inputBits n))=Switch.terminalDepth n := rfl
end ThreeSum.LightSwitchDepth
