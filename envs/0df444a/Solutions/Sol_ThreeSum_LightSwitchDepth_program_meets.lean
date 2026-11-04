-- Prove2me | solution 1 for ThreeSum.LightSwitchDepth.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:31:01.400316+00:00
-- url     : https://prove2.me/submissions/9609ee8e-e768-4104-af8d-36f329cea4ec

import Definitions.Def_Submission_ThreeSum_LightSwitch
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Theorems.Thm_ThreeSum_LightSwitchDepth_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSwitch_meets


set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchDepth
open Light
variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J d : ℕ}
namespace ThreeSum.LightSwitchDepth
theorem _root_.solution (hword : (word J : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim program 0 d [J] μ (time J)
      (fun result ν => result=(depth J : ℤ) ∧ ν=μ) := meets rfl rfl hword hd
end ThreeSum.LightSwitchDepth
