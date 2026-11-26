-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.e_pow2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:25.982733+00:00
-- url     : https://prove2.me/submissions/c04ede6e-be23-410a-82b1-98cbb7659fa6

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (k : ℕ) : e (2 ^ k) = {k} := by
  ext i
  simp [e, Nat.testBit_two_pow]
end Scott1976.DataTypesAsLattices
