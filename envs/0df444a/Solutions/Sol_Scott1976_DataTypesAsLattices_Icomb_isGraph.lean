-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.Icomb_isGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:50.533201+00:00
-- url     : https://prove2.me/submissions/ec444563-1f0a-4183-b6e8-7fb65ed76594

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality
import Theorems.Thm_Scott1976_DataTypesAsLattices_Icomb_app
import Theorems.Thm_Scott1976_DataTypesAsLattices_graph_ext


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution : Icomb = graph (fun x => funOf Icomb x) := by
  apply graph_ext
  intro x
  rw [Icomb_app]
end Scott1976.DataTypesAsLattices
