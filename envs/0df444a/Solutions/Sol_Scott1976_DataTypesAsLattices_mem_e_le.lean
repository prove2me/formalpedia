-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.mem_e_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:57:48.867803+00:00
-- url     : https://prove2.me/submissions/bad075a3-b90c-4869-b61d-4ae34f1e09ad

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Theorems.Thm_Scott1976_DataTypesAsLattices_two_pow_le_of_testBit
import Theorems.Thm_Scott1976_DataTypesAsLattices_le_two_pow

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {n k : ℕ} (h : k ∈ e n) : k ≤ n :=
  (le_two_pow k).trans (two_pow_le_of_testBit h)
end Scott1976.DataTypesAsLattices
