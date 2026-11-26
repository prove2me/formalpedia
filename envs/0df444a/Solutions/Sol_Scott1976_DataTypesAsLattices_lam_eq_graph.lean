-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.lam_eq_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:21.153596+00:00
-- url     : https://prove2.me/submissions/8be9d44c-c186-4fe3-8bd3-ed672ac6273f

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (τ : Pomega → Pomega) : lam τ = graph τ := rfl
end Scott1976.DataTypesAsLattices
