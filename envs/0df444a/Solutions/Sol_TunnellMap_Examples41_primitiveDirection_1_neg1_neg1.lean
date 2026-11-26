-- Prove2me | solution 1 for TunnellMap.Examples41.primitiveDirection_1_neg1_neg1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:03:56.669671+00:00
-- url     : https://prove2.me/submissions/9d5885c7-2a06-4d33-a451-0f47b74b960b

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
import Theorems.Thm_TunnellMap_Examples41_tripleContent_eq_one_of_x_one
import Theorems.Thm_TunnellMap_primitiveDirection_eq_self_of_content_one_of_oriented


set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    primitiveDirection ⟨1, -1, -1⟩ = ⟨1, -1, -1⟩ := by
  apply primitiveDirection_eq_self_of_content_one_of_oriented
  · exact tripleContent_eq_one_of_x_one (-1) (-1)
  · norm_num [FirstNonzeroPositive]
end TunnellMap.Examples41
