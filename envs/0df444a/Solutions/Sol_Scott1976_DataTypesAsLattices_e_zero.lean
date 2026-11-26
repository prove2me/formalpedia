-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.e_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:27.054575+00:00
-- url     : https://prove2.me/submissions/880f44ba-3b76-4834-a771-03836b56a743

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
theorem _root_.solution : e 0 = ∅ := by
  ext k
  simp [e]
end Scott1976.DataTypesAsLattices
