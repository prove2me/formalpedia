-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.isOpen_memOpen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:57:37.819383+00:00
-- url     : https://prove2.me/submissions/cb52c97c-9191-4478-be62-03768bff39e3

import Mathlib.Topology.Order
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (k : ℕ) : IsOpen (memOpen k) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨k, rfl⟩
end Scott1976.DataTypesAsLattices
