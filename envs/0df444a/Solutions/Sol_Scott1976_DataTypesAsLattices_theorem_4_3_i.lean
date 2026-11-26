-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_4_3_i
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:38.573124+00:00
-- url     : https://prove2.me/submissions/631686ce-aa47-4203-9f9e-5bcaee9d27a1

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Theorems.Thm_Scott1976_DataTypesAsLattices_comp_app
import Theorems.Thm_Scott1976_DataTypesAsLattices_graph_ext
import Theorems.Thm_Scott1976_DataTypesAsLattices_retract_app
import Theorems.Thm_Scott1976_DataTypesAsLattices_arrowR_app
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
theorem _root_.solution {a b u : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    funOf (arrowR a b) (funOf (arrowR a b) u) = funOf (arrowR a b) u := by
  rw [arrowR_app, arrowR_app]
  apply graph_ext
  intro x
  simp [comp_app, retract_app ha, retract_app hb]
end Scott1976.DataTypesAsLattices
