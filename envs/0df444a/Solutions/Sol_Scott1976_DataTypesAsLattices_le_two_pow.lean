-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:57:13.940358+00:00
-- url     : https://prove2.me/submissions/3d6a95da-4fe6-4a02-a0f4-8d1ea0019198

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    calc
      k + 1 ≤ 2 ^ k + 1 := Nat.succ_le_succ ih
      _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left Nat.one_le_two_pow _
      _ = 2 ^ k * 2 := (Nat.mul_two (2 ^ k)).symm
      _ = 2 ^ (k + 1) := (Nat.pow_succ 2 k).symm
end Scott1976.DataTypesAsLattices
