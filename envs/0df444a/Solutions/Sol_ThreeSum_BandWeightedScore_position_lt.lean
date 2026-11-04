-- Prove2me | solution 1 for ThreeSum.BandWeightedScore.position_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:22:55.312074+00:00
-- url     : https://prove2.me/submissions/39a0b7bd-169a-4041-9873-3a0466fc0553

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
theorem _root_.solution {n g a i : ℕ} (hi : i < length n g a) : a*g+i < n := by
  have hh := min_le_right g (n-a*g)
  unfold length at hi
  omega
end ThreeSum.BandWeightedScore
