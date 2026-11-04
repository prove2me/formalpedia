-- Prove2me | solution 1 for ThreeSum.LightPrimePool.mem_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:11:12.370214+00:00
-- url     : https://prove2.me/submissions/6b30b5ed-bfe5-43f9-8362-48db6044893e

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Theorems.Thm_ThreeSum_LightPrimePool_mem_prefix

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimePool
theorem _root_.solution {y p : ℕ} :
    p ∈ values y ↔ Nat.Prime p ∧ y < p ∧ p ≤ 4*y := by
  rw [values,mem_prefix]
  constructor
  · rintro ⟨hp,hlo,hhi⟩
    exact ⟨hp,hlo,by omega⟩
  · rintro ⟨hp,hlo,hhi⟩
    exact ⟨hp,hlo,by omega⟩
end ThreeSum.LightPrimePool
