-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.pairElem_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:59.254123+00:00
-- url     : https://prove2.me/submissions/fba73ba9-0d3c-4fb3-9bf9-47340025bd1e

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality
import Theorems.Thm_Scott1976_DataTypesAsLattices_seq2_app_one


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (x y : Pomega) : funOf (pairElem x y) (ofNat 1) = y :=
  seq2_app_one x y
end Scott1976.DataTypesAsLattices
