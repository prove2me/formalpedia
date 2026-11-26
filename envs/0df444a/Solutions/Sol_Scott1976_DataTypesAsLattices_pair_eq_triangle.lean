-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.pair_eq_triangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:57:21.631243+00:00
-- url     : https://prove2.me/submissions/b3bcced4-ae98-4e41-9da5-f7d0aa86910b

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (n m : ℕ) : pair n m = triangle (n + m) + m := rfl
end Scott1976.DataTypesAsLattices
