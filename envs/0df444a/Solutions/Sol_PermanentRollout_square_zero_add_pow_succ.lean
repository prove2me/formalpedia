-- Prove2me | solution 1 for PermanentRollout.square_zero_add_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/67c0a632-7e83-46cb-b760-15128f3b9936

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {R : Type*} [CommSemiring R]
    {x y : R} {n : ℕ} (hx : x ^ 2 = 0) (hy : y ^ (n + 1) = 0) :
    (x + y) ^ (n + 1) = (n + 1 : ℕ) * x * y ^ n := by
  classical
  rw [add_pow, Finset.sum_eq_single 1]
  · simp [Nat.choose_one_right, mul_assoc, mul_comm, mul_left_comm]
  · intro j _ hj
    by_cases hzero : j = 0
    · subst j
      simp [hy]
    · have htwo : 2 ≤ j := by omega
      simp [pow_eq_zero_of_le htwo hx]
  · simp
end PermanentRollout
