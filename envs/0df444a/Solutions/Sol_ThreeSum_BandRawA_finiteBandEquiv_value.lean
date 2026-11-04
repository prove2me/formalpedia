-- Prove2me | solution 1 for ThreeSum.BandRawA.finiteBandEquiv_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:54:28.788554+00:00
-- url     : https://prove2.me/submissions/b002b17a-6c75-4f53-829d-eb522716d13f

import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution (n g a : ℕ) (f : ℕ → ℤ) (j : Fin (bandLength n g a)) :
    f (finiteBandEquiv n g a j).val.val=f (BandPartition.start g a+j.val) := rfl
end ThreeSum.BandRawA
