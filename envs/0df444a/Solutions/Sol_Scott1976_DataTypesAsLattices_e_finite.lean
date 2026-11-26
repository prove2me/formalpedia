-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.e_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:14.092631+00:00
-- url     : https://prove2.me/submissions/3f49b36e-4c82-43a0-8d79-cf7365f30a87

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e_le

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (n : ℕ) : (e n).Finite :=
  (Finset.range (n + 1)).finite_toSet.subset fun _k hk =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_e_le hk))
end Scott1976.DataTypesAsLattices
