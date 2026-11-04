-- Prove2me | solution 1 for ThreeSum.LightSourceFlagArray.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:59:21.571093+00:00
-- url     : https://prove2.me/submissions/b107786e-56cc-4729-adbc-fb75f35e6e65

import Definitions.Def_Submission_ThreeSum_LightSourceMaskFlags
import Definitions.Def_Submission_ThreeSum_LightSourceFlagArray
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightSourceMaskFlags_time_bound
import Theorems.Thm_ThreeSum_LightSourceRowFlag_time_bound
import Theorems.Thm_ThreeSum_LightSourceTrim_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceFlagArray
open Light SourceFlagProduct
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceFlagArray
theorem _root_.solution (n J L U : ℕ) :
    time n J L U ≤ n*(300*(J*L+1)^2+
      J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+400)+10 := by
  have hh := LightSourceMaskFlags.time_bound J L U
  unfold time
  exact Nat.add_le_add_right (Nat.mul_le_mul_left n (by omega)) 10
end ThreeSum.LightSourceFlagArray
