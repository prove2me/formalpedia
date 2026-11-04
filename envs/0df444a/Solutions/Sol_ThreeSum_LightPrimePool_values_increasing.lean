-- Prove2me | solution 1 for ThreeSum.LightPrimePool.values_increasing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:54:02.818727+00:00
-- url     : https://prove2.me/submissions/c4bf310e-d593-45be-8c4c-930d7550ed8a

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_WeightedCache3SUM_Alias_ec6abe6e008eb668

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimePool
theorem _root_.solution (y : ℕ) : (values y).Pairwise (· < ·) := prefix_increasing y (3*y)
end ThreeSum.LightPrimePool
