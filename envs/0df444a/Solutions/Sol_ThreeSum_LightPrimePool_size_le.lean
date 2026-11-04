-- Prove2me | solution 1 for ThreeSum.LightPrimePool.size_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:11:11.266491+00:00
-- url     : https://prove2.me/submissions/c7e268c4-6ad1-48b6-a1f1-9c95102d00eb

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Theorems.Thm_ThreeSum_LightPrimePool_prefix_length_le

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimePool
theorem _root_.solution (y : ℕ) : size y ≤ 3*y := prefix_length_le y (3*y)
end ThreeSum.LightPrimePool
