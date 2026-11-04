-- Prove2me | solution 1 for ThreeSum.LightSourceBandSetup.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:26:02.436373+00:00
-- url     : https://prove2.me/submissions/88835941-c89b-4c3b-b702-48bd98d86b33

import Definitions.Def_Submission_ThreeSum_LightSourceBandBatch
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightBlockSourceHashes_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSourceBandBatch_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketFromHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketOriginal_time_bound
import Theorems.Thm_ThreeSum_LightSourceBuild_time_bound
import Theorems.Thm_ThreeSum_LightSourceGather_time_bound
import Theorems.Thm_ThreeSum_LightSourceHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound
import Theorems.Thm_ThreeSum_LightSourceRetainedStages_time_bound
import Theorems.Thm_ThreeSum_LightSourceStages_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandSetup
open Light BandPartition SourceBandLayout
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBandSetup
theorem _root_.solution (n g p m U D : ℕ) (hg : 0 < g) :
    time n g p m U D ≤ 1016*n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
      size n g*(233*m+1713)+560 := by
  have hb := LightSourceBandBatch.time_bound n g p m U D hg
  have hdiv : LightSmallDivide.time (n-1) g ≤ 20*n+40 := by
    have hh := Nat.div_le_self (n-1) g
    unfold LightSmallDivide.time
    omega
  have hn : n ≤ n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  unfold time
  nlinarith
end ThreeSum.LightSourceBandSetup
