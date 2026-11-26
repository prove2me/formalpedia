-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.seq2_app
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:21.31504+00:00
-- url     : https://prove2.me/submissions/f2866597-f9e4-4a85-b255-b0e0fc8da1b1

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_seq2_body_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_beta


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (x y z : Pomega) :
    funOf (seq2 x y) z = condSet z x (condSet (predSet z) y botElem) :=
  beta (seq2_body_isScottContinuous x y) z
end Scott1976.DataTypesAsLattices
