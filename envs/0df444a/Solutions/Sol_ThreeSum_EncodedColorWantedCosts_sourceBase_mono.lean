-- Prove2me | solution 1 for ThreeSum.EncodedColorWantedCosts.sourceBase_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:03:13.236654+00:00
-- url     : https://prove2.me/submissions/3451e962-d030-42a0-8dbd-f3cdf5c9477d

import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_sourceBase_eq

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedCosts
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
namespace ThreeSum.EncodedColorWantedCosts
theorem _root_.solution {free M h J len len' : ℕ} (hlen : len ≤ len') :
    sourceBase free M h J len ≤ sourceBase free M h J len' := by
  rw [sourceBase_eq,sourceBase_eq]
  gcongr
end ThreeSum.EncodedColorWantedCosts
