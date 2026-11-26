-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.comp_isScottContinuous_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:00:36.744226+00:00
-- url     : https://prove2.me/submissions/e4a4b420-8e1e-4264-9895-d5ebdeb963ef

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_isScottContinuous_left
import Theorems.Thm_Scott1976_DataTypesAsLattices_graph_const_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_3


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (u : Pomega) :
    IsScottContinuous (fun v => comp u v) :=
  graph_const_isScottContinuous (fun v x => funOf u (funOf v x))
    (fun x => theorem_1_3 (funOf_isScottContinuous u) (funOf_isScottContinuous_left x))
end Scott1976.DataTypesAsLattices
