-- Prove2me | solution 1 for P2M_Scott1976_DataTypesAsLattices_lt_two_pow__acf4439c4153
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:09.782846+00:00
-- url     : https://prove2.me/submissions/481d94c0-8740-4bb5-a36c-b01c2f83cb68

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (k : ℕ) : k < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    calc
      k + 1 ≤ 2 ^ k := Nat.succ_le_of_lt ih
      _ < 2 ^ k + 2 ^ k := Nat.lt_add_of_pos_right (Nat.two_pow_pos k)
      _ = 2 ^ (k + 1) := by rw [← Nat.two_mul, Nat.mul_comm, Nat.pow_succ]
end Scott1976.DataTypesAsLattices
