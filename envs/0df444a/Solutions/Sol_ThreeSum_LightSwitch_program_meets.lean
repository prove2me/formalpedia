-- Prove2me | solution 1 for ThreeSum.LightSwitch.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:25:25.976905+00:00
-- url     : https://prove2.me/submissions/c2ee94ed-bb30-47b3-a271-2c47de6018ba

import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar
import Definitions.Def_Submission_ThreeSum_LightSwitch
import Theorems.Thm_ThreeSum_LightSwitch_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J j r q d : ℕ}
namespace ThreeSum.LightSwitch
theorem _root_.solution (hj : j ≤ J) (hne : (Switch.candidates J j r).Nonempty)
    (hword : (word J r : ℤ) ≤ lim.word) :
    Meets lim program 0 d [J,j,r] μ (time r)
      (fun result ν => result=(Switch.switchIndex J j r : ℤ) ∧ ν=μ) :=
  meets rfl hj hne hword
end ThreeSum.LightSwitch
