-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.Ycomb_app
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:00:31.375219+00:00
-- url     : https://prove2.me/submissions/dcd6c7f4-99f9-4ac6-a3a8-761de9858e8d

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_diagApp_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_omegaComb_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_beta
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_3


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (u : Pomega) :
    funOf Ycomb u = funOf (omegaComb u) (omegaComb u) :=
  beta (theorem_1_3 diagApp_isScottContinuous omegaComb_isScottContinuous) u
end Scott1976.DataTypesAsLattices
