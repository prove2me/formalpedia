-- Prove2me | solution 1 for OddPerfectNumber.prime_power_sigma_euler_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T11:10:55.634873+00:00
-- url     : https://prove2.me/submissions/8996dd80-fb82-4fa0-9a3e-30db3ba5db82

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

theorem solution (q a : Nat)
    (hq : 1 < q) :
    (q - 1) * (∑ i ∈ Finset.range (a + 1), q ^ i) < q ^ (a + 1) := by
  calc
    (q - 1) * (∑ i ∈ Finset.range (a + 1), q ^ i) =
        q ^ (a + 1) - 1 := by
      rw [Nat.mul_comm]
      exact OddPerfectNumber.geom_mul_sub_one q (a + 1) (by omega)
    _ < q ^ (a + 1) := by
      exact Nat.sub_lt (pow_pos (by omega) _) Nat.one_pos
