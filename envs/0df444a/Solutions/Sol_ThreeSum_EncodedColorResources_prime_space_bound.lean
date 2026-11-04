-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.prime_space_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:23:40.136598+00:00
-- url     : https://prove2.me/submissions/7310cd20-a9d9-4cf9-8ee2-3ba216bb37aa

import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Theorems.Thm_ThreeSum_EncodedColorResources_normalized_space_bound
import Theorems.Thm_ThreeSum_EncodedColorResources_prime_address_bound
import Theorems.Thm_ThreeSum_EncodedColorResources_prime_core_space_bound
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface
set_option maxHeartbeats 2400000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (free n U : ℕ) :
    LightEncodedColorPrimeHost.inputSpace free n U ≤ free+2000*(scale n)^3+U := by
  have hb := (scale_bounds n).1
  have hnrm := normalized_space_bound free n
  have hprime := prime_address_bound free n
  have hcore := prime_core_space_bound (prime free n (bandSize n)) n U
  have hp3 : scale n ≤ (scale n)^3 := Nat.le_self_pow (by decide) _
  unfold LightEncodedColorPrimeHost.inputSpace
  apply max_le <;> nlinarith only [hb,hnrm,hprime,hcore,hp3]
end ThreeSum.EncodedColorResources
