-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.Kcomb_app
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:16.422698+00:00
-- url     : https://prove2.me/submissions/eb3e3cff-5ad4-428a-b71d-35b9e6c86bd2

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality
import Theorems.Thm_Scott1976_DataTypesAsLattices_beta
import Theorems.Thm_Scott1976_DataTypesAsLattices_graph_const_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_id_isScottContinuous


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (x : Pomega) :
    funOf Kcomb x = graph (fun _ => x) :=
  beta (graph_const_isScottContinuous (fun x _ => x)
    (fun _ => id_isScottContinuous)) x
end Scott1976.DataTypesAsLattices
