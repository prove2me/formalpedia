-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.comp_right_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:00:39.63037+00:00
-- url     : https://prove2.me/submissions/12832b31-fbdc-4d83-a6c6-62178243162f

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_isScottContinuous_left
import Theorems.Thm_Scott1976_DataTypesAsLattices_graph_const_isScottContinuous


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (a : Pomega) :
    IsScottContinuous (fun u => comp u a) :=
  graph_const_isScottContinuous (fun u x => funOf u (funOf a x))
    (fun x => funOf_isScottContinuous_left (funOf a x))
end Scott1976.DataTypesAsLattices
