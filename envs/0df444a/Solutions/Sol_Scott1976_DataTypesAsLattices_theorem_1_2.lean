-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:18.209487+00:00
-- url     : https://prove2.me/submissions/90d49780-45ca-43a9-9468-1360284dd703

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_2_i
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_2_ii
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_2_iii

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega} (hf : IsScottContinuous f) (u : Pomega) :
    funOf (graph f) = f ∧ u ⊆ graph (funOf u) ∧
      (graph (funOf u) = u ↔ IsGraph u) :=
  ⟨theorem_1_2_i hf, theorem_1_2_ii u, theorem_1_2_iii u⟩
end Scott1976.DataTypesAsLattices
