-- Prove2me | solution 1 for ThreeSum.LightPrimePool.values_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:58:02.879325+00:00
-- url     : https://prove2.me/submissions/fd217bdc-a418-4d66-a9e8-c0b238353242

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Theorems.Thm_ThreeSum_LightPrimePool_prefix_nodup

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimePool
theorem _root_.solution (y : ℕ) : (values y).Nodup := prefix_nodup y (3*y)
end ThreeSum.LightPrimePool
