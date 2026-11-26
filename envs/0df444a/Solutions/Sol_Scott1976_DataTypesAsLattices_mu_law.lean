-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.mu_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:17.619167+00:00
-- url     : https://prove2.me/submissions/f597e4cc-9274-4349-839a-0cafde967336

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_monotone_right
import Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_monotone_left

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {u v x y : Pomega} (hu : u ⊆ v) (hx : x ⊆ y) :
    funOf u x ⊆ funOf v y :=
  subset_trans (funOf_monotone_left hu x) (funOf_monotone_right v hx)
end Scott1976.DataTypesAsLattices
