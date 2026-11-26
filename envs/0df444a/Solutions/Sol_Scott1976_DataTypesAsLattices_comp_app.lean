-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.comp_app
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:00:24.543813+00:00
-- url     : https://prove2.me/submissions/1604d7db-579b-46c6-bdf0-abb403232e41

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Theorems.Thm_Scott1976_DataTypesAsLattices_beta
import Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_3


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (u v x : Pomega) :
    funOf (comp u v) x = funOf u (funOf v x) :=
  beta (theorem_1_3 (funOf_isScottContinuous u) (funOf_isScottContinuous v)) x
end Scott1976.DataTypesAsLattices
