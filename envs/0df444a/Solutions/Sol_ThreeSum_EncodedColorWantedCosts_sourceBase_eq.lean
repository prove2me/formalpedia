-- Prove2me | solution 1 for ThreeSum.EncodedColorWantedCosts.sourceBase_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:47:24.801327+00:00
-- url     : https://prove2.me/submissions/60a9881e-4d51-4162-97d4-29bc5aed0b74

import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Theorems.Thm_Light_Ends_next


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedCosts
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
namespace ThreeSum.EncodedColorWantedCosts
theorem _root_.solution (free M h J len : ℕ) :
    sourceBase free M h J len=LightCoverKeyData.keyEnd free h J+
      6*len+2*LightGuardedWanted.totalKeys h J+3*M+5+
      2*(3*len*LightGuardedWanted.totalKeys h J/M) := by
  unfold sourceBase LightWantedSetup.pairBase LightSourceBucketSetup.next LightWantedSetup.bucketBase
    LightWantedSetup.rightCodes LightWantedSetup.leftCodes LightGuardedWanted.wantedFree
  omega
end ThreeSum.EncodedColorWantedCosts
