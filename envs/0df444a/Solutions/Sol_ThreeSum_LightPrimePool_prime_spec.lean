-- Prove2me | solution 1 for ThreeSum.LightPrimePool.prime_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:15:36.090983+00:00
-- url     : https://prove2.me/submissions/3ab8e6be-d22d-4ac5-8d65-5008251b35ee

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Theorems.Thm_ThreeSum_LightPrimePool_mem_values
import Theorems.Thm_ThreeSum_LightPrimePool_prime_mem

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimePool
theorem _root_.solution {y i : ℕ} (hi : i < size y) :
    Nat.Prime (prime y i) ∧ y < prime y i ∧ prime y i ≤ 4*y :=
  mem_values.mp (prime_mem hi)
end ThreeSum.LightPrimePool
