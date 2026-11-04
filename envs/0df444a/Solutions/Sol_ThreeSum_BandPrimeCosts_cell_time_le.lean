-- Prove2me | solution 1 for ThreeSum.BandPrimeCosts.cell_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:01:46.334604+00:00
-- url     : https://prove2.me/submissions/01d3988a-1a86-4cdb-ac54-1481fa268af5

import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Definitions.Def_Submission_ThreeSum_BandPrimeCosts

set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Scales BandScales CostLedger ArithmeticStageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace ThreeSum.BandPrimeCosts
theorem _root_.solution (p g s U : ℕ) :
    LightBandWeightedScoreCell.time p g s U ≤ (s+1)*unit p g U := by
  unfold LightBandWeightedScoreCell.time LightBandWeightedScoreSlice.time
    LightWeightedScore.runtimeTime LightWeightedScore.time unit
  nlinarith
end ThreeSum.BandPrimeCosts
