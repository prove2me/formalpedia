-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.typicalG_isScottOpen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:55.083525+00:00
-- url     : https://prove2.me/submissions/7af1f9ed-1d2a-4ea7-83d4-26f79b34b275

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Classification
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_6_1
import Theorems.Thm_Scott1976_DataTypesAsLattices_id_isScottContinuous


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution : IsScottOpen typicalG :=
  ((theorem_6_1).1 (fun x => x) id_isScottContinuous)
end Scott1976.DataTypesAsLattices
