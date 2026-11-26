-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.mem_topElem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:52:54.911+00:00
-- url     : https://prove2.me/submissions/f6dc1f60-d3bf-45a8-92f9-ec7140892316

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (n : ℕ) : n ∈ topElem := Set.mem_univ n
end Scott1976.DataTypesAsLattices
