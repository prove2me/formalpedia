-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.triangle_le_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:57:22.807571+00:00
-- url     : https://prove2.me/submissions/e280e0eb-efbb-47f4-bad1-079c17d24801

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Theorems.Thm_Scott1976_DataTypesAsLattices_triangle_succ

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (n m : ℕ) :
    triangle (n + m) ≤ pair n m ∧ pair n m < triangle (n + m + 1) := by
  constructor
  · exact Nat.le_add_right _ _
  · rw [triangle_succ]
    exact Nat.add_lt_add_left (Nat.lt_succ_of_le (Nat.le_add_left m n)) _
end Scott1976.DataTypesAsLattices
