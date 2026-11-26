-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.beta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:50.379518+00:00
-- url     : https://prove2.me/submissions/7c4b84bd-f14f-4f24-ab8d-fb0f160b82c1

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_2_i
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem



set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {τ : Pomega → Pomega} (hτ : IsScottContinuous τ) (y : Pomega) :
    funOf (lam τ) y = τ y := by
  simp [lam, theorem_1_2_i hτ]
end Scott1976.DataTypesAsLattices
