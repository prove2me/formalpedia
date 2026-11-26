-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.mem_funOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:16.899054+00:00
-- url     : https://prove2.me/submissions/574e6102-a65c-4843-b047-369cadc90ae1

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {u x : Pomega} {m : ℕ} :
    m ∈ funOf u x ↔ ∃ n, e n ⊆ x ∧ pair n m ∈ u := Iff.rfl
end Scott1976.DataTypesAsLattices
