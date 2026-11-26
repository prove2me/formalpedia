-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_1_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:58.078014+00:00
-- url     : https://prove2.me/submissions/278797b7-6c7f-45a8-9dd3-f630f07902fa

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_3_comp

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (fun x => f (g x)) :=
  theorem_1_3_comp hf hg
end Scott1976.DataTypesAsLattices
