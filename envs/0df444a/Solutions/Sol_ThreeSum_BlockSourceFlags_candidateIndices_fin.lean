-- Prove2me | solution 1 for ThreeSum.BlockSourceFlags.candidateIndices_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:52:08.016714+00:00
-- url     : https://prove2.me/submissions/2a00eb77-9ba6-46f2-8916-116d0cee9180

import Definitions.Def_Submission_ThreeSum_BlockSourceRows
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockSourceFlags

set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceFlags
open BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open LocalHashMoments LocalCoverBounds GlobalEncoding
set_option maxHeartbeats 1200000
namespace ThreeSum.BlockSourceFlags
theorem _root_.solution (h : ℕ) (s : Occurrence h) :
    candidateIndices h s.val = LightLocalCoverSchedule.candidateAt h s := rfl
end ThreeSum.BlockSourceFlags
