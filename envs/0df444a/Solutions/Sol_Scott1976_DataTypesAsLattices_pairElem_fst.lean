-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.pairElem_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:58.715527+00:00
-- url     : https://prove2.me/submissions/335827d6-1c96-4839-b8c3-a13ce56965cc

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality
import Theorems.Thm_Scott1976_DataTypesAsLattices_seq2_app_zero


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (x y : Pomega) : funOf (pairElem x y) (ofNat 0) = x :=
  seq2_app_zero x y
end Scott1976.DataTypesAsLattices
