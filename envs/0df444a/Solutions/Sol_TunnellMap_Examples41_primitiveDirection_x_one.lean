-- Prove2me | solution 1 for TunnellMap.Examples41.primitiveDirection_x_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:27:01.282178+00:00
-- url     : https://prove2.me/submissions/2da32dce-be2e-4e07-a19e-1c80ede8261d

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
import Theorems.Thm_TunnellMap_Examples41_tripleContent_eq_one_of_x_one
import Theorems.Thm_TunnellMap_primitiveDirection_eq_self_of_content_one_of_oriented


set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution (y z : ℤ) :
    primitiveDirection ⟨1, y, z⟩ = ⟨1, y, z⟩ := by
  apply primitiveDirection_eq_self_of_content_one_of_oriented
  · exact tripleContent_eq_one_of_x_one y z
  · exact Or.inl (by norm_num)
end TunnellMap.Examples41
