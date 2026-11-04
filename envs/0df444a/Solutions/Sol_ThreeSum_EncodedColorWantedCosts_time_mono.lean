-- Prove2me | solution 1 for ThreeSum.EncodedColorWantedCosts.time_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:52:09.514442+00:00
-- url     : https://prove2.me/submissions/b17e5945-cda3-463d-88a4-cd2b2a88d143

import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_keyBound_mono

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedCosts
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
namespace ThreeSum.EncodedColorWantedCosts
theorem _root_.solution {P P' M h J U len len' : ℕ} (hP : P ≤ P') (hlen : len ≤ len') :
    time P M h J U len ≤ time P' M h J U len' := by
  have hkey := keyBound_mono (h := h) (J := J) hP
  unfold time LightRawAKeys.time LightOriginalOffset.time LightResidueHistogram.time
    LightResidues.residuesTime LightResidues.residueBudget LightHistogram.histogramTime
    LightHistogram.countTime LightReportingAffine.time
  gcongr
end ThreeSum.EncodedColorWantedCosts
