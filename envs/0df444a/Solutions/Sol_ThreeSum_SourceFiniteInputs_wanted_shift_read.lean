-- Prove2me | solution 1 for ThreeSum.SourceFiniteInputs.wanted_shift_read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:21:56.547799+00:00
-- url     : https://prove2.me/submissions/60eff70c-d50c-437a-a85d-819ab5dd83d2

import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs

set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteInputs
open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule
namespace ThreeSum.SourceFiniteInputs
theorem _root_.solution {μ : ℕ → ℤ} {free M P h J : ℕ} [NeZero M] {xs : List ℤ}
    (H : LightWantedSetup.Output μ (LightGuardedWanted.wantedFree free h J xs.length) M
      (LightGuardedWanted.left P xs) (LightGuardedWanted.right h J)
      (3*xs.length) (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M P xs h J)) :
    μ (LightGuardedWanted.wantedFree free h J xs.length+3)=(RawAKeyLists.selected M P xs h J : ℤ) :=
  H.2.2.2.1
end ThreeSum.SourceFiniteInputs
