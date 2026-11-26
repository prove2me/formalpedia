-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.mem_botElem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:52:54.007538+00:00
-- url     : https://prove2.me/submissions/20705204-ce0b-472a-a3b0-50c3d76d02da

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (n : ℕ) : n ∈ botElem ↔ False := by simp [botElem]
end Scott1976.DataTypesAsLattices
