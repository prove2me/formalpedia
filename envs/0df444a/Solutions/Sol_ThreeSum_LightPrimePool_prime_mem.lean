-- Prove2me | solution 1 for ThreeSum.LightPrimePool.prime_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:06:32.929256+00:00
-- url     : https://prove2.me/submissions/d9e4bdc8-8b2f-4771-96ad-40eb046e02c4

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimePool
theorem _root_.solution {y i : ℕ} (hi : i < size y) : prime y i ∈ values y := by
  unfold prime
  rw [List.getD_eq_getElem _ _ hi]
  exact List.mem_of_getElem rfl
end ThreeSum.LightPrimePool
