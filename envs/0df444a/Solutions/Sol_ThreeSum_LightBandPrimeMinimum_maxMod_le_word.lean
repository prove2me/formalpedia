-- Prove2me | solution 1 for ThreeSum.LightBandPrimeMinimum.maxMod_le_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:37:27.467905+00:00
-- url     : https://prove2.me/submissions/37aab365-fd5d-4069-a23c-811089a9575f

import Definitions.Def_Submission_ThreeSum_LightBandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandPrimeChoice
import Definitions.Def_Submission_ThreeSum_LightBandPrimeMinimum

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeMinimum
open Light BandCandidateRows BandWeightedScore BandPrimeChoice
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThreeSum.LightBandPrimeMinimum
theorem _root_.solution (maxMod nA nB nC g R s U : ℕ) :
    maxMod ≤ LightBandWeightedScore.word maxMod nA nB nC g R s U := by
  unfold LightBandWeightedScore.word LightBandWeightedScoreCell.word LightWeightedScore.word
  omega
end ThreeSum.LightBandPrimeMinimum
