-- Prove2me | solution 1 for ThreeSum.BandPrimeCosts.minimum_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:55.431644+00:00
-- url     : https://prove2.me/submissions/50bb9869-df1c-4d2e-bf02-15b8774f7764

import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
import Theorems.Thm_ThreeSum_BandPrimeCosts_unit_ge
import Definitions.Def_WeightedCache3SUM_Alias_3fbba4f4a826c815

set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Scales BandScales CostLedger ArithmeticStageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace ThreeSum.BandPrimeCosts
theorem _root_.solution (p g R s U : ℕ) :
    LightBandPrimeMinimum.time p g R s U ≤ 3*(R+1)*(s+1)^2*unit p g U := by
  have hv : 1000 ≤ (R+1)*(s+1)*unit p g U :=
    (unit_ge p g U).trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hh := aggregate_time_le p g R s U
  calc
    _ = (s+1)*(LightBandWeightedScore.time p g R s U+140) := by
      unfold LightBandPrimeMinimum.time; ring
    _ ≤ (s+1)*(3*((R+1)*(s+1)*unit p g U)) := by
      apply Nat.mul_le_mul_left
      nlinarith
    _ = _ := by ring
end ThreeSum.BandPrimeCosts
