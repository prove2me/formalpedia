-- Prove2me | solution 1 for ThreeSum.BandPrimeCosts.aggregate_time_le_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:07:32.846244+00:00
-- url     : https://prove2.me/submissions/5f29ceb2-25b2-4df4-ba99-77402aa5ef5d

import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
import Theorems.Thm_ThreeSum_BandPrimeCosts_unit_ge
import Theorems.Thm_ThreeSum_BandPrimeCosts_cell_time_le

set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Scales BandScales CostLedger ArithmeticStageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace ThreeSum.BandPrimeCosts
theorem _root_.solution (p g R s U : ℕ) :
    LightBandWeightedScore.time p g R s U ≤ 2*(R+1)*(s+1)*unit p g U := by
  have hc := Nat.mul_le_mul_left R (Nat.add_le_add_right (cell_time_le p g s U) 100)
  have hv : 1000 ≤ (s+1)*unit p g U :=
    (unit_ge p g U).trans (Nat.le_mul_of_pos_left _ (by omega))
  calc
    _ ≤ R*((s+1)*unit p g U+100)+50 := Nat.add_le_add_right hc 50
    _ ≤ R*(2*((s+1)*unit p g U))+(s+1)*unit p g U := by
      apply Nat.add_le_add
      · apply Nat.mul_le_mul_left; omega
      · omega
    _ ≤ 2*(R+1)*((s+1)*unit p g U) := by nlinarith
    _ = _ := by ring
end ThreeSum.BandPrimeCosts
