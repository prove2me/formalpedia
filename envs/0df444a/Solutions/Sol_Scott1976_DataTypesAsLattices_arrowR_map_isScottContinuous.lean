-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.arrowR_map_isScottContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:12.986356+00:00
-- url     : https://prove2.me/submissions/ab08f1fe-504d-4622-bdc6-e598b83f6364

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Theorems.Thm_Scott1976_DataTypesAsLattices_comp_isScottContinuous_right
import Theorems.Thm_Scott1976_DataTypesAsLattices_comp_right_const
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_3


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (a b : Pomega) :
    IsScottContinuous (fun u => comp b (comp u a)) :=
  theorem_1_3 (comp_isScottContinuous_right b) (comp_right_const a)
end Scott1976.DataTypesAsLattices
