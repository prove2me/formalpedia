-- Prove2me | solution 1 for ThreeSum.EncodedColorWantedCosts.keyBound_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:41:12.61847+00:00
-- url     : https://prove2.me/submissions/61719a15-b78a-4cd8-8ebb-567a4256b96c

import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedCosts
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
namespace ThreeSum.EncodedColorWantedCosts
theorem _root_.solution {P P' h J : ℕ} (hP : P ≤ P') :
    LightGuardedWanted.keyBound P h J ≤ LightGuardedWanted.keyBound P' h J := by
  unfold LightGuardedWanted.keyBound
  omega
end ThreeSum.EncodedColorWantedCosts
