-- Prove2me | solution 1 for PermanentRollout.subtree_mul_add_pow_eq_of_annihilates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/a66a7a2c-fec2-45bd-938a-0346db2b140d

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommSemiring R] (p x z : R)
    (hp : p * z = 0) (d : ℕ) :
    p * (x + z) ^ d = p * x ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc
      p * (x + z) ^ (d + 1) =
          (p * (x + z) ^ d) * (x + z) := by
            rw [pow_succ, mul_assoc]
      _ = (p * x ^ d) * (x + z) := by rw [ih]
      _ = p * x ^ (d + 1) := by
        rw [mul_add]
        have hzero : (p * x ^ d) * z = 0 := by
          calc
            (p * x ^ d) * z = (p * z) * x ^ d := by ring
            _ = 0 := by rw [hp, zero_mul]
        rw [hzero, add_zero, pow_succ, mul_assoc]
end PermanentRollout
