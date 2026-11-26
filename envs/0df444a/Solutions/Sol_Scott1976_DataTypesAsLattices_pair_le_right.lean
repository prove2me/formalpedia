-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.pair_le_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:57.62132+00:00
-- url     : https://prove2.me/submissions/91f4ddb5-1a01-4b85-8e28-80d65da1905d

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (n m : ℕ) : m ≤ pair n m :=
  Nat.le_add_left _ _
end Scott1976.DataTypesAsLattices
