-- Prove2me | solution 1 for ThreeSum.LightBlockSourceRetainedProgram.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:41.776579+00:00
-- url     : https://prove2.me/submissions/fa0589e3-02b6-4c80-9107-5fa56275ad9b

import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedHost
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedProgram
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
    LightBlockSourceRetainedHost.time h J cut ≤
      1200*(J*(512*h)+1)^2*(downsetCap (J*(512*h)) cut+1)+
      300*(J+1)*(512*h+1)+600*(J*(512*h)+1)*(downsetCap (J*(512*h)) cut+1)+
      downsetCap (J*(512*h)) cut*(300*(J*(512*h)+1)^2+
        J*(150*(512*h)+464*(Nat.log 2 ((512*h)*localPrime h+1)+1)+250)+400)+
      314*downsetCap (J*(512*h)) cut*(Nat.log 2 (endpointBound h J+1)+1)+
      12000*(J*(512*h)+1)^4*(downsetCap (J*(512*h)) cut+1)+1122 := by
  have he := LightDownsetEnumerationSetup.time_bound hcut
  have hp := LightSourcePreparation.time_bound (downsetCap (J*(512*h)) cut) J (512*h) (localPrime h)
  have hs := LightSourceRetainedStages.time_bound (E := endpointBound h J) hcut
  unfold LightBlockSourceRetainedHost.time
  nlinarith
end ThreeSum.LightBlockSourceRetainedProgram
