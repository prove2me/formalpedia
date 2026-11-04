-- Prove2me | solution 1 for ThreeSum.LightPrimePool.prime_strictly_increasing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:58:32.86614+00:00
-- url     : https://prove2.me/submissions/1b111761-f280-4bd9-b4a5-b1b4a75529db

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Theorems.Thm_ThreeSum_LightPrimePool_values_increasing

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimePool
theorem _root_.solution {y i j : ℕ}
    (hi : i < size y) (hj : j < size y) (hij : i < j) : prime y i < prime y j := by
  unfold prime
  rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj]
  exact List.pairwise_iff_getElem.mp (values_increasing y) i j hi hj hij
end ThreeSum.LightPrimePool
