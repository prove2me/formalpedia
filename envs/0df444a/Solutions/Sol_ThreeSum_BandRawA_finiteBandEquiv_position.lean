-- Prove2me | solution 1 for ThreeSum.BandRawA.finiteBandEquiv_position
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:54:27.58313+00:00
-- url     : https://prove2.me/submissions/82090185-db9e-4b0a-b3b3-cb0f82a78e40

import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution (n g a : ℕ) (j : Fin (bandLength n g a)) :
    (finiteBandEquiv n g a j).val.val=BandPartition.start g a+j.val := rfl
end ThreeSum.BandRawA
