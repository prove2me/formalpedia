-- Prove2me | solution 1 for ThreeSum.LightBalancedWanted.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:35:51.951182+00:00
-- url     : https://prove2.me/submissions/31872084-2d86-44a6-b978-7fbcda05a6fa

import Definitions.Def_Submission_ThreeSum_LightWantedSetup
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted
import Theorems.Thm_ThreeSum_LightBalancedWanted_total_le_div
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
import Theorems.Thm_ThreeSum_LightWantedSetup_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightBalancedWanted
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits}
namespace ThreeSum.LightBalancedWanted
theorem _root_.solution (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR U : ℕ) :
    time M left right NL NR U ≤ LightOriginalOffset.time M NL NR U+
      2000*(NL+NR+M+NL*NR/M+1)*(Nat.log 2 (U+1)+Nat.log 2 (M+M+1)+1)+100 := by
  have hh := LightWantedSetup.time_bound M left right NL NR U M
    (LightOriginalOffset.selected M left right NL NR)
  have hc := total_le_div M left right NL NR
  calc
    time M left right NL NR U ≤ LightOriginalOffset.time M NL NR U+
      2000*(NL+NR+M+total M left right NL NR (LightOriginalOffset.selected M left right NL NR)+1)*
        (Nat.log 2 (U+1)+Nat.log 2 (M+M+1)+1)+100 := by unfold time; omega
    _ ≤ _ := by gcongr
end ThreeSum.LightBalancedWanted
