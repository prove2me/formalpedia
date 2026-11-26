-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.mem_e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:52:55.526193+00:00
-- url     : https://prove2.me/submissions/0545a63d-340d-432f-89b6-ef012788f0b5

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {n k : ℕ} : k ∈ e n ↔ n.testBit k := Iff.rfl
end Scott1976.DataTypesAsLattices
