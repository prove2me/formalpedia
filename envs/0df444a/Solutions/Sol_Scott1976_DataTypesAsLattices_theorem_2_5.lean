-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_2_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:24.491407+00:00
-- url     : https://prove2.me/submissions/5aea0ff1-598c-477a-af32-a758b01a2681

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_Ycomb_app
import Theorems.Thm_Scott1976_DataTypesAsLattices_omega_first_recursion

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf Ycomb (graph f) = fix f := by
  rw [Ycomb_app]
  exact omega_first_recursion hf
end Scott1976.DataTypesAsLattices
