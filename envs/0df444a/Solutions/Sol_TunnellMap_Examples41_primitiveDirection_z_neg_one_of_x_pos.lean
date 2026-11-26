-- Prove2me | solution 1 for TunnellMap.Examples41.primitiveDirection_z_neg_one_of_x_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:05:46.850386+00:00
-- url     : https://prove2.me/submissions/a4c8d2a4-9cf5-4874-bea5-8072d4876857

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
import Theorems.Thm_TunnellMap_Examples41_tripleContent_eq_one_of_z_neg_one
import Theorems.Thm_TunnellMap_primitiveDirection_eq_self_of_content_one_of_oriented


set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution (x y : ℤ) (hx : 0 < x) :
    primitiveDirection ⟨x, y, -1⟩ = ⟨x, y, -1⟩ := by
  apply primitiveDirection_eq_self_of_content_one_of_oriented
  · exact tripleContent_eq_one_of_z_neg_one x y
  · exact Or.inl hx
end TunnellMap.Examples41
