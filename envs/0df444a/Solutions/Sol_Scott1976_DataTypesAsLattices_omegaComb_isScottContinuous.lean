-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.omegaComb_isScottContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:09.175423+00:00
-- url     : https://prove2.me/submissions/7a3dc894-4230-425b-a28f-db2679670853

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_isScottContinuous_left
import Theorems.Thm_Scott1976_DataTypesAsLattices_graph_const_isScottContinuous

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution : IsScottContinuous omegaComb :=
  graph_const_isScottContinuous
    (fun u x => funOf u (funOf x x))
    (fun x => funOf_isScottContinuous_left (funOf x x))
end Scott1976.DataTypesAsLattices
