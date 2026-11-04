-- Prove2me | solution 1 for ThreeSum.LightLocalCoverTables.entry_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:36.888541+00:00
-- url     : https://prove2.me/submissions/d210a2a2-e053-44a7-9298-c1b62a0bf174

import Definitions.Def_Submission_ThreeSum_LightLocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightLocalCoverTables

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverTables
open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
theorem _root_.solution (h j r : ℕ) :
    LightLocalCoverCandidate.entry (512*h) (LocalMaskGraph.vertexCount (512*h) h)
      (localPrime h) (localBucketCap h) (LocalMaskGraph.maskAt (512*h) h)
      (LocalCoverMatrix.bits (512*h) h)
      (LocalMaskHashes.coeff false (candidate h j))
      (LocalMaskHashes.coeff true (candidate h j)) r = matrix h j r := rfl
end ThreeSum.LightLocalCoverTables
