-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.omegaComb_app
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:00:27.792812+00:00
-- url     : https://prove2.me/submissions/953ec6f7-c983-49fe-8cbf-a210ad50e569

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_diagApp_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_beta
import Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_3


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (u x : Pomega) :
    funOf (omegaComb u) x = funOf u (funOf x x) :=
  beta (theorem_1_3 (funOf_isScottContinuous u) diagApp_isScottContinuous) x
end Scott1976.DataTypesAsLattices
