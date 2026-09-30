-- Prove2me | solution 1 for ShiQMAErrorIteration.copies_roundsFor_le
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-30T06:59:31.812982+00:00
-- url     : https://prove2.me/submissions/9129fbd8-80a8-4ba5-ba60-62f64b8fce2c

import Definitions.Def_ShiQMAErrorIteration

set_option autoImplicit false
open ShiQMAErrorIteration

/-- The number of copies required by these rounds is polynomial in the target exponent. -/
theorem solution (m : Nat) (hm : 0 < m) : 3 ^ roundsFor m ≤ 81 * m ^ 2 := by
  have hlog := Nat.pow_log_le_self 2 (Nat.ne_of_gt hm)
  have hbase : 3 ^ Nat.log 2 m ≤ 4 ^ Nat.log 2 m :=
    Nat.pow_le_pow_left (by decide : 3 ≤ 4) _
  have hsq : (2 ^ Nat.log 2 m) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hlog 2
  have heq : 4 ^ Nat.log 2 m = (2 ^ Nat.log 2 m) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm]
    exact (pow_mul 2 2 (Nat.log 2 m)).symm
  rw [heq] at hbase
  dsimp [roundsFor]
  rw [pow_add]
  norm_num only [show (3 : Nat) ^ 4 = 81 by norm_num]
  nlinarith
