-- Prove2me | solution 1 for ThreeSum.LightSourceMaskFlags.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:53:14.477684+00:00
-- url     : https://prove2.me/submissions/764d1812-5793-4619-922e-ec85708a4adc

import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_Submission_ThreeSum_LightSourceMaskFlags
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightSourceRowFlag_time_bound
import Theorems.Thm_ThreeSum_LightSourceTrim_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceMaskFlags
open Light SourceFlagProduct
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceMaskFlags
theorem _root_.solution (J L U : ℕ) :
    time J L U ≤ 300*(J*L+1)^2+
      J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+200 := by
  have hb := LightMaskBits.time_bound (J*L)
  have ht := LightSourceTrim.time_bound J L U
  unfold time
  omega
end ThreeSum.LightSourceMaskFlags
