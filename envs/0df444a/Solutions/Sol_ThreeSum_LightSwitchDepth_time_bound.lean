-- Prove2me | solution 1 for ThreeSum.LightSwitchDepth.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:15:58.983572+00:00
-- url     : https://prove2.me/submissions/cdb14393-2ee0-4359-b42c-65984c7521a8

import Definitions.Def_Submission_ThreeSum_LightSwitch
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchDepth
open Light
variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J d : ℕ}
namespace ThreeSum.LightSwitchDepth
theorem _root_.solution (J : ℕ) : time J ≤ 260*J+90 := by
  have hh := LightSmallDivide.time_bound (13*J) 20
  unfold time
  omega
end ThreeSum.LightSwitchDepth
