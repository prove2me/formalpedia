-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.mem_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:57:40.647949+00:00
-- url     : https://prove2.me/submissions/e30e1c41-eaee-43af-9c53-a0ec79df34fb

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega} {p : ℕ} :
    p ∈ graph f ↔ ∃ n m, p = pair n m ∧ m ∈ f (e n) := Iff.rfl
end Scott1976.DataTypesAsLattices
