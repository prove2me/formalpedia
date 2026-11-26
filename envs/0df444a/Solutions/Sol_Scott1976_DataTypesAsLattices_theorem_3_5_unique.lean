-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_3_5_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:05.599192+00:00
-- url     : https://prove2.me/submissions/04226db6-602d-42fc-bf47-559d0ed5c9f2

import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
import Definitions.Def_Scott1976_DataTypesAsLattices_Enumeration
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
theorem _root_.solution {q q' : Pomega → Pomega}
    (hq : IsScottContinuous q) (hq' : IsScottContinuous q')
    (h : ∀ n, q (e n) = q' (e n)) (x : Pomega) : q x = q' x := by
  rw [hq, hq']
  ext k
  simp [scottUnion, scottPiece, h]
end Scott1976.DataTypesAsLattices
