-- Prove2me | solution 1 for ThreeSum.LightWantedSetup.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:17:21.446257+00:00
-- url     : https://prove2.me/submissions/5a72ed22-f408-4fc6-b781-d87298be3cc0

import Definitions.Def_Submission_ThreeSum_LightWantedJoin
import Definitions.Def_Submission_ThreeSum_WantedResidueKeys
import Definitions.Def_Submission_ThreeSum_LightSourceBucketSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightWantedSetup
import Theorems.Thm_ThreeSum_LightBalancedOffset_time_bound
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeys_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_957e2f25efb6cbcf
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketBuild_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketFromHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketSetup_time_bound
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound
import Theorems.Thm_ThreeSum_LightWantedJoin_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightWantedSetup
open Light WantedResidueKeys
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : Limits}
namespace ThreeSum.LightWantedSetup
theorem _root_.solution (M : ℕ) (left right : ℕ → ℤ) (NL NR U D : ℕ) (shift : ℤ) :
    time M left right NL NR U D shift ≤
      2000*(NL+NR+M+total M left right NL NR shift+1)*
        (Nat.log 2 (U+1)+Nat.log 2 (M+D+1)+1) := by
  have hL := LightSourceResidues.time_bound NL M U D
  have hR := LightSourceResidues.time_bound NR M U D
  have hB := LightSourceBucketSetup.time_bound NR M
  have hJ := LightWantedJoin.time_bound (fun i => code M shift (left i))
    (fun j => code M 0 (right j)) NR NL
  change LightWantedJoin.time _ _ NR NL ≤ 400*(NL+total M left right NL NR shift+1) at hJ
  unfold time
  nlinarith
end ThreeSum.LightWantedSetup
