-- Prove2me | solution 1 for ThreeSum.BandWeightedScore.end_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:54:46.748876+00:00
-- url     : https://prove2.me/submissions/65fdea09-efb6-4fdc-831b-3b592e4fad28

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
theorem _root_.solution {n g a : ℕ} (ha : a*g ≤ n) : a*g+length n g a ≤ n := by
  have hh := min_le_right g (n-a*g)
  unfold length
  omega
end ThreeSum.BandWeightedScore
