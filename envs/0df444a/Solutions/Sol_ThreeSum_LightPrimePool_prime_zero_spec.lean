-- Prove2me | solution 1 for ThreeSum.LightPrimePool.prime_zero_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:14:11.922193+00:00
-- url     : https://prove2.me/submissions/1a3ea428-e5dc-4696-909b-fd709489d695

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Theorems.Thm_ThreeSum_LightPrimePool_mem_values
import Theorems.Thm_ThreeSum_LightPrimePool_prime_spec
import Theorems.Thm_ThreeSum_LightPrimePool_size_pos
import Theorems.Thm_ThreeSum_LightPrimePool_prime_zero_le_mem

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimePool
theorem _root_.solution {y : ℕ} (hy : 0 < y) :
    Nat.Prime (prime y 0) ∧ y < prime y 0 ∧ prime y 0 ≤ 2*y := by
  have hp := prime_spec (size_pos hy)
  obtain ⟨p,hpr,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul y hy.ne'
  have hmem : p ∈ values y := mem_values.mpr ⟨hpr,hlo,by omega⟩
  exact ⟨hp.1,hp.2.1,(prime_zero_le_mem hmem).trans hhi⟩
end ThreeSum.LightPrimePool
