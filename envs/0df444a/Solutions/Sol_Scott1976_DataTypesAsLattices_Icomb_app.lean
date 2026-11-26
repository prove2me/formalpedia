-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.Icomb_app
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:17.230928+00:00
-- url     : https://prove2.me/submissions/d8015b21-3d22-4d0c-b4ac-782fd1493c90

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Theorems.Thm_Scott1976_DataTypesAsLattices_beta
import Theorems.Thm_Scott1976_DataTypesAsLattices_id_isScottContinuous


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (x : Pomega) : funOf Icomb x = x :=
  beta id_isScottContinuous x
end Scott1976.DataTypesAsLattices
