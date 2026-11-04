-- Prove2me | solution 1 for ThreeSum.LightSelectedPrime.prime_zero_eq_selectedPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:24.282472+00:00
-- url     : https://prove2.me/submissions/0ea76f8f-c4a7-424c-9e0e-11ee256d4d4f

import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSum_LightSelectedPrime
import Theorems.Thm_ThreeSum_LightPrimePool_mem_values
import Theorems.Thm_ThreeSum_LightPrimePool_prime_zero_le_mem
import Theorems.Thm_ThreeSum_LightPrimePool_prime_zero_spec
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_spec


set_option autoImplicit false
open ThreeSum ThreeSum.LightSelectedPrime
open Light LocalCoverBounds LightResidues
set_option maxHeartbeats 1000000
namespace ThreeSum.LightSelectedPrime
theorem _root_.solution (N : ℕ) :
    LightPrimePool.prime (rootCeiling N) 0 = selectedPrime N := by
  apply Nat.le_antisymm
  · have hs := selectedPrime_spec N
    apply LightPrimePool.prime_zero_le_mem
    exact LightPrimePool.mem_values.mpr ⟨hs.1,hs.2.1,by omega⟩
  · unfold selectedPrime
    apply Finset.min'_le
    exact mem_primeCandidates.mpr
      (LightPrimePool.prime_zero_spec (rootCeiling_pos N))
end ThreeSum.LightSelectedPrime
