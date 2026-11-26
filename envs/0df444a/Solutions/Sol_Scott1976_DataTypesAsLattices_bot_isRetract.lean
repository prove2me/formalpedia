-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.bot_isRetract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:17.455396+00:00
-- url     : https://prove2.me/submissions/0e3c07f8-68aa-4686-97bb-af0c12335468

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_ofNat
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem



set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution : IsRetract botElem := by
  unfold IsRetract comp botElem
  ext p
  simp [graph, funOf]
end Scott1976.DataTypesAsLattices
