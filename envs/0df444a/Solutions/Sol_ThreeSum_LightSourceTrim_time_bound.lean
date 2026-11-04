-- Prove2me | solution 1 for ThreeSum.LightSourceTrim.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:47:12.558209+00:00
-- url     : https://prove2.me/submissions/e00310b6-7ed4-4cda-9522-b7382b1187af

import Definitions.Def_Submission_ThreeSum_LightSourceRowFlag
import Definitions.Def_Submission_ThreeSum_SourceFlagProduct
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightSourceRowFlag_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceTrim
open Light SourceFlagProduct
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceTrim
theorem _root_.solution (J L U : ℕ) :
    time J L U ≤ J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+100 := by
  have hh := LightSourceRowFlag.time_bound L U
  unfold time
  exact Nat.add_le_add_right (Nat.mul_le_mul_left J (Nat.add_le_add_right hh 250)) 100
end ThreeSum.LightSourceTrim
