-- Prove2me | solution 1 for ThreeSum.EncodedColorWantedCosts.word_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:52:33.430639+00:00
-- url     : https://prove2.me/submissions/cde48300-101c-40be-b0f5-e04fa443dc8c

import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_keyBound_mono

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedCosts
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
namespace ThreeSum.EncodedColorWantedCosts
theorem _root_.solution {P P' M h J U len len' : ℕ} (hP : P ≤ P') (hlen : len ≤ len') :
    LightGuardedWanted.word P M h J U len ≤ LightGuardedWanted.word P' M h J U len' := by
  have hkey := keyBound_mono (h := h) (J := J) hP
  unfold LightGuardedWanted.word LightRawAKeys.word LightBalancedWanted.word
    LightOriginalOffset.word LightKaratsuba.wordBound LightSourceResidues.word
  gcongr
end ThreeSum.EncodedColorWantedCosts
