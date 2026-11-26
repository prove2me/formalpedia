-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_7_3_i
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:13.599858+00:00
-- url     : https://prove2.me/submissions/f6cbfc3a-2ae3-424f-8401-bcc4b13623da

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality
import Theorems.Thm_Scott1976_DataTypesAsLattices_Icomb_isGraph
import Theorems.Thm_Scott1976_DataTypesAsLattices_Icomb_app
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
theorem _root_.solution (A : RestrictedEquiv) :
    (arrowE A A).mem Icomb :=
  ⟨Icomb_isGraph, Icomb_isGraph, fun x y hxy => by simpa [Icomb_app] using hxy⟩
end Scott1976.DataTypesAsLattices
