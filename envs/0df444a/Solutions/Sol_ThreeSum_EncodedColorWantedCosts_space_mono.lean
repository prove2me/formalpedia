-- Prove2me | solution 1 for ThreeSum.EncodedColorWantedCosts.space_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:16:47.353196+00:00
-- url     : https://prove2.me/submissions/764fe33f-d30b-47d9-a678-260900ae7238

import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_keyBound_mono
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_sourceBase_mono
import Theorems.Thm_Light_Ends_next


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedCosts
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
namespace ThreeSum.EncodedColorWantedCosts
theorem _root_.solution {free P P' M h J U len len' : ℕ} (hP : P ≤ P') (hlen : len ≤ len') :
    space free P M h J U len ≤ space free P' M h J U len' := by
  have hkey := keyBound_mono (h := h) (J := J) hP
  have hbase := sourceBase_mono (free := free) (M := M) (h := h) (J := J) hlen
  unfold space LightRawAKeys.space LightOriginalOffset.space LightSourceResidues.space
    LightWantedSetup.pairBase LightSourceBucketSetup.next LightWantedSetup.bucketBase
    LightWantedSetup.rightCodes LightWantedSetup.leftCodes LightGuardedWanted.wantedFree
  gcongr
end ThreeSum.EncodedColorWantedCosts
