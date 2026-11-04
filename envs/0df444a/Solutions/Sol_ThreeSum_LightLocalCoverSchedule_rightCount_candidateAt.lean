-- Prove2me | solution 1 for ThreeSum.LightLocalCoverSchedule.rightCount_candidateAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:03.048776+00:00
-- url     : https://prove2.me/submissions/8649bd63-311e-4361-8892-5922cab0edd8

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTransport
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSum_LightCoverGreedy
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_candidateAt_mapAt
import Theorems.Thm_ThreeSum_LocalMaskHashes_right_count


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverSchedule
open Finset LocalHashMoments LocalCoverBounds GlobalEncoding
namespace ThreeSum.LightLocalCoverSchedule
theorem _root_.solution (h : ℕ) (s : Occurrence h) {r : ℕ} (hr : r < localPrime h) :
    LocalCoverMatrix.rightCount (candidate h (candidateAt h s)) h r =
      HashFamily.bucketSize (LocalGraph.rightVertices (512*h) h) (mapAt h s) (r : LocalField h) := by
  unfold LocalCoverMatrix.rightCount
  rw [LocalMaskHashes.right_count _ hr,candidateAt_mapAt]
end ThreeSum.LightLocalCoverSchedule
