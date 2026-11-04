-- Prove2me | solution 1 for ThreeSum.LightBlockSourceRetainedProgram.time_le_factor_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:26:38.21788+00:00
-- url     : https://prove2.me/submissions/113d5a2c-7d65-4eea-b87f-4034f80aa43c

import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedHost
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedProgram
import Theorems.Thm_ThreeSum_LightBlockSourceRetainedProgram_time_bound
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightBlockSourceHashes_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_432686f9c1a6224e
import Definitions.Def_WeightedCache3SUM_Alias_f1b1ba0c94539568
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightLocalCoverRow_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Theorems.Thm_ThreeSum_LightPairFlags_time_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSourceBuild_time_bound
import Theorems.Thm_ThreeSum_LightSourceFlagArray_time_bound
import Theorems.Thm_ThreeSum_LightSourceGather_time_bound
import Theorems.Thm_ThreeSum_LightSourceHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceMaskFlags_time_bound
import Theorems.Thm_ThreeSum_LightSourcePreparation_time_bound
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound
import Theorems.Thm_ThreeSum_LightSourceRetainedStages_time_bound
import Theorems.Thm_ThreeSum_LightSourceRowFlag_time_bound
import Theorems.Thm_ThreeSum_LightSourceStages_time_bound
import Theorems.Thm_ThreeSum_LightSourceTrim_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightWeightDecode_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceRetainedProgram
open Light LightPascal LightSubsetAddress LightBlockSourceRetainedHost
open LocalCoverBounds SubsetAddress BlockSourceEncoding LightBlockSourceBuild
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
namespace ThreeSum.LightBlockSourceRetainedProgram
theorem _root_.solution {h J cut : ℕ} (hcut : cut ≤ J*(512*h)) :
    LightBlockSourceRetainedHost.time h J cut ≤ factor h J*(downsetCap (J*(512*h)) cut+1) := by
  have ht := time_bound hcut
  have hc := Nat.le_succ (downsetCap (J*(512*h)) cut)
  have hsetup : 300*(J+1)*(512*h+1) ≤
      300*(J+1)*(512*h+1)*(downsetCap (J*(512*h)) cut+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have htrim := Nat.mul_le_mul_right
    (300*(J*(512*h)+1)^2+J*(150*(512*h)+464*(Nat.log 2 ((512*h)*localPrime h+1)+1)+250)+400) hc
  have hg := Nat.mul_le_mul_left (314*(Nat.log 2 (endpointBound h J+1)+1)) hc
  have hconst : 1122 ≤ 1122*(downsetCap (J*(512*h)) cut+1) := by omega
  unfold factor
  nlinarith
end ThreeSum.LightBlockSourceRetainedProgram
