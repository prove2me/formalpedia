-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.arrowR_app
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:48.866717+00:00
-- url     : https://prove2.me/submissions/cfd785c7-b0d5-4f0d-af2f-3759d2045729

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Theorems.Thm_Scott1976_DataTypesAsLattices_arrowR_map_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_beta


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (a b u : Pomega) :
    funOf (arrowR a b) u = comp b (comp u a) :=
  beta (arrowR_map_isScottContinuous a b) u
end Scott1976.DataTypesAsLattices
