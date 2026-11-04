-- Prove2me | solution 1 for ThreeSum.BandWeightedScore.length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:22:36.135956+00:00
-- url     : https://prove2.me/submissions/86dc4e00-c364-48a2-8b24-aea6165cda94

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
theorem _root_.solution (n g a : ℕ) : length n g a ≤ g := min_le_left _ _
end ThreeSum.BandWeightedScore
