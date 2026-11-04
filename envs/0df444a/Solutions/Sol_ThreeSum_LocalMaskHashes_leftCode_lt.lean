-- Prove2me | solution 1 for ThreeSum.LocalMaskHashes.leftCode_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:07:18.734804+00:00
-- url     : https://prove2.me/submissions/5b297db9-7e19-4974-b4d1-943107f4e256

import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Definitions.Def_Submission_ThreeSum_LightHashHistogram
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
import Theorems.Thm_ThreeSum_LightResidues_residue_lt
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos


set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskHashes
open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds
variable {h L k : ℕ}
namespace ThreeSum.LocalMaskHashes
theorem _root_.solution (w : Weight L (LocalField h)) (k i : ℕ) :
    leftCode w k i < localPrime h := by
  unfold leftCode LightHashHistogram.code
  exact LightResidues.residue_lt (localPrime_pos h) 1 _
end ThreeSum.LocalMaskHashes
