-- Prove2me | solution 1 for ThreeSum.LightPrimePool.prime_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:03:26.72413+00:00
-- url     : https://prove2.me/submissions/305ccbcc-6f0d-4503-b1a7-8096b7d777b9

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Theorems.Thm_ThreeSum_LightPrimePool_values_nodup

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimePool
theorem _root_.solution {y i j : ℕ} (hi : i < size y) (hj : j < size y)
    (heq : prime y i = prime y j) : i = j :=
  (List.getD_inj hi hj (values_nodup y)).mp heq
end ThreeSum.LightPrimePool
