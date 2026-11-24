-- Prove2me | solution 1 for ULHC.side_mem_cellE_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:40:26.774481+00:00
-- url     : https://prove2.me/submissions/487e7116-61a3-4403-a240-69108fc0034a

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
import Theorems.Thm_ULHC_cell_of_side
import Theorems.Thm_ULHC_side_mem_cellE
import Theorems.Thm_ULHC_side_mem_cellE_nb


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (c : Pt) (tf : Side) (x : Pt) :
    sideEdge c tf ∈ cellE x ↔ x = c ∨ x = nb c tf :=
  ⟨fun h => cell_of_side c h, fun h => by
    rcases h with rfl | rfl
    · exact side_mem_cellE _ tf
    · exact side_mem_cellE_nb _ tf⟩
end ULHC
