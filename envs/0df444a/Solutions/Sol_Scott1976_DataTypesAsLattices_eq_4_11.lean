-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.eq_4_11
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:27.778385+00:00
-- url     : https://prove2.me/submissions/1fb73fdd-43d1-4e28-a727-de62f2f125ae

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Theorems.Thm_Scott1976_DataTypesAsLattices_arrowR_app

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (a b a' b' u : Pomega) :
    funOf (arrowR a b) (funOf (arrowR a' b') u) =
      comp b (comp (comp b' (comp u a')) a) := by
  rw [arrowR_app, arrowR_app]
end Scott1976.DataTypesAsLattices
