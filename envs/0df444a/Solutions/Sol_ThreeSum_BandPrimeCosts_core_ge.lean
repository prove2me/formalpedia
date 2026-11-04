-- Prove2me | solution 1 for ThreeSum.BandPrimeCosts.core_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:01:58.387975+00:00
-- url     : https://prove2.me/submissions/ddcfcc09-b61e-49fb-b2db-d229750524e7

import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
import Theorems.Thm_ThreeSum_BandPrimeCosts_unit_ge

set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Scales BandScales CostLedger ArithmeticStageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace ThreeSum.BandPrimeCosts
theorem _root_.solution (p g R s U : ℕ) : 1000 ≤ core p g R s U := by
  have hp : 0 < (R+1)*(s+1)^2 := by positivity
  exact (unit_ge p g U).trans (Nat.le_mul_of_pos_left _ hp)
end ThreeSum.BandPrimeCosts
