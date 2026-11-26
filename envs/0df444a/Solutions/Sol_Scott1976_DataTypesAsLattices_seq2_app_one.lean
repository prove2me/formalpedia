-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.seq2_app_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:06.676678+00:00
-- url     : https://prove2.me/submissions/4debabce-55bb-4be9-9938-d8d083f9a6b4

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_seq2_app
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem


attribute [local simp] Scott1976.DataTypesAsLattices.mem_ofNat

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (x y : Pomega) : funOf (seq2 x y) (ofNat 1) = y := by
  rw [seq2_app]
  ext n
  simp [condSet, predSet, ofNat, botElem]
end Scott1976.DataTypesAsLattices
