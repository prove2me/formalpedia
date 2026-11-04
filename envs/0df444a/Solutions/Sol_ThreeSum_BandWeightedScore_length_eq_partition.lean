-- Prove2me | solution 1 for ThreeSum.BandWeightedScore.length_eq_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:54:44.954211+00:00
-- url     : https://prove2.me/submissions/b4a14720-64ee-4099-ab77-ca478a3454c2

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Definitions.Def_Submission_ThreeSum_BandWeightedScore

set_option autoImplicit false
open ThreeSum ThreeSum.BandWeightedScore
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
namespace ThreeSum.BandWeightedScore
theorem _root_.solution (n g a : ℕ) :
    length n g a=BandPartition.stop n g a-BandPartition.start g a := by
  unfold length BandPartition.stop BandPartition.start
  rw [Nat.add_mul,Nat.one_mul]
  omega
end ThreeSum.BandWeightedScore
