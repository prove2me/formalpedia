-- Prove2me | solution 1 for ThreeSum.BandPrimeCosts.unit_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:55:49.655224+00:00
-- url     : https://prove2.me/submissions/4ae83ba7-2d7c-47c6-9acb-265cb14b34e1

import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Definitions.Def_Submission_ThreeSum_BandPrimeCosts

set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Scales BandScales CostLedger ArithmeticStageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace ThreeSum.BandPrimeCosts
theorem _root_.solution (p g U : ℕ) : 1000 ≤ unit p g U := by unfold unit; omega
end ThreeSum.BandPrimeCosts
