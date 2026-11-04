-- Prove2me | solution 1 for ThreeSum.LightSourceStages.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:03:24.196649+00:00
-- url     : https://prove2.me/submissions/34ace9d2-c4db-43c1-a374-2c06b630dc7a

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightSourceBuild_time_bound
import Theorems.Thm_ThreeSum_LightSourceGather_time_bound
import Theorems.Thm_ThreeSum_LightSourceHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceStages
open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceStages
theorem _root_.solution {N L cut p m U D E : ℕ} (hcut : cut ≤ L) :
    time N L cut p m U D E ≤
      278*N*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
      157*downsetCap L cut*(Nat.log 2 (E+1)+1)+13*m+
      6000*(L+1)^4*(downsetCap L cut+1)+269 := by
  have hs := LightSourceBuild.time_bound N (downsetCap L cut) p m U D E
  have hz := LightZetaStages.time_bound hcut
  unfold time
  omega
end ThreeSum.LightSourceStages
