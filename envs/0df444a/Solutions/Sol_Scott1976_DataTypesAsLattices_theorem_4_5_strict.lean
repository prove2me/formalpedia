-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_4_5_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:44.684407+00:00
-- url     : https://prove2.me/submissions/afa748a6-9506-4352-b688-f7418d2e4b65

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
theorem _root_.solution (a b : Pomega) :
    condSet botElem
      (pairSeq (ofNat 0) (funOf a botElem))
      (pairSeq (ofNat 1) (funOf b botElem)) = botElem := by
  ext n
  simp [condSet, botElem]
end Scott1976.DataTypesAsLattices
