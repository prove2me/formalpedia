-- Prove2me | solution 1 for ThreeSum.LightSourcePreparation.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:05:45.336118+00:00
-- url     : https://prove2.me/submissions/6a74a412-da8f-47a0-b68a-c06f7b59ee26

import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_Submission_ThreeSum_LightSourceFlagArray
import Definitions.Def_Submission_ThreeSum_LightSourcePreparation
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightBlockSourceHashes_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Theorems.Thm_ThreeSum_LightSourceFlagArray_time_bound
import Theorems.Thm_ThreeSum_LightSourceMaskFlags_time_bound
import Theorems.Thm_ThreeSum_LightSourceRowFlag_time_bound
import Theorems.Thm_ThreeSum_LightSourceTrim_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourcePreparation
open Light BlockCoefficientRows
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourcePreparation
theorem _root_.solution (n J L U : ℕ) :
    time n J L U ≤ 300*(J+1)*(L+1)+600*(J*L+1)*(n+1)+
      n*(300*(J*L+1)^2+J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+400)+410 := by
  have hh := LightBlockSourceHashes.time_bound J L n
  have hf := LightSourceFlagArray.time_bound n J L U
  unfold time
  omega
end ThreeSum.LightSourcePreparation
