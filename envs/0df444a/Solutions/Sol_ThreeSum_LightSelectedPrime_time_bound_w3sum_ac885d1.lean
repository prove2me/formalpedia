-- Prove2me | solution 1 for ThreeSum.LightSelectedPrime.time_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:45:18.012587+00:00
-- url     : https://prove2.me/submissions/be72391f-74c0-4c58-aa70-04f6430095e8

import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSum_LightSelectedPrime
import Theorems.Thm_ThreeSum_LightSelectedPrime_pool_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSelectedPrime
open Light LocalCoverBounds LightResidues
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSelectedPrime
theorem _root_.solution (N : ℕ) : time N ≤ 6000*(N+2)^3 := by
  have hy : rootCeiling N ≤ N+1 := by
    unfold rootCeiling
    have hh := Nat.sqrt_le_self (N-1)
    omega
  have hp := pool_time_bound (rootCeiling N)
  have hs := Nat.sqrt_le_self (N-1)
  have hpow := Nat.pow_le_pow_left (show rootCeiling N+1 ≤ N+2 by omega) 3
  have hp' : LightPrimePool.time (rootCeiling N) ≤ 5000*(N+2)^3 :=
    hp.trans (Nat.mul_le_mul_left _ hpow)
  have hlinear : 18*Nat.sqrt (N-1)+112 ≤ 1000*(N+2)^3 := by
    have hl : 18*Nat.sqrt (N-1)+112 ≤ 1000*(N+2) := by omega
    exact hl.trans (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide : 3 ≠ 0) (N+2)))
  unfold time sqrtTime
  omega
end ThreeSum.LightSelectedPrime
