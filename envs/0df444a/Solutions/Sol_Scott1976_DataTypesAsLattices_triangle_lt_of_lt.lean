-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.triangle_lt_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:54.644073+00:00
-- url     : https://prove2.me/submissions/bfec4f7d-adf6-4a1d-8a3d-8ee7027e8a60

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Theorems.Thm_Scott1976_DataTypesAsLattices_triangle_succ
import Theorems.Thm_Scott1976_DataTypesAsLattices_triangle_le_of_le

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {a b : ℕ} (h : a < b) : triangle a < triangle b := by
  have : a + 1 ≤ b := Nat.succ_le_of_lt h
  calc
    triangle a < triangle a + (a + 1) := Nat.lt_add_of_pos_right (Nat.succ_pos _)
    _ = triangle (a + 1) := (triangle_succ a).symm
    _ ≤ triangle b := triangle_le_of_le this
end Scott1976.DataTypesAsLattices
