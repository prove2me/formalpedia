-- Prove2me | solution 1 for ThreeSum.LightLocalCoverSchedule.leftCount_candidateAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:01.695194+00:00
-- url     : https://prove2.me/submissions/b8e465cf-4acc-409c-99da-d3afcfdeaaac

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTransport
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSum_LightCoverGreedy
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_candidateAt_mapAt
import Theorems.Thm_ThreeSum_LocalMaskHashes_left_count


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverSchedule
open Finset LocalHashMoments LocalCoverBounds GlobalEncoding
namespace ThreeSum.LightLocalCoverSchedule
theorem _root_.solution (h : ℕ) (s : Occurrence h) {r : ℕ} (hr : r < localPrime h) :
    LocalCoverMatrix.leftCount (candidate h (candidateAt h s)) h r =
      HashFamily.bucketSize (LocalGraph.leftVertices (512*h) h) (mapAt h s) (r : LocalField h) := by
  unfold LocalCoverMatrix.leftCount
  rw [LocalMaskHashes.left_count _ hr,candidateAt_mapAt]
end ThreeSum.LightLocalCoverSchedule
