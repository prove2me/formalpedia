-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_6_4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:36.985714+00:00
-- url     : https://prove2.me/submissions/daa6c715-74b0-41ff-95b8-3f333689b7ab

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Classification
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
theorem _root_.solution :
    {ofNat 0} = {x : Pomega | x ⊆ ofNat 0} ∩ {x | 0 ∈ x} := by
  ext x
  constructor
  · intro hx
    have hx' : x = ofNat 0 := hx
    rw [hx']
    change ofNat 0 ⊆ ofNat 0 ∧ 0 ∈ ofNat 0
    simp [ofNat]
  · intro ⟨hsub, h0⟩
    ext n
    simp [ofNat]
    constructor
    · intro hn; exact hsub hn
    · intro hn; simpa [hn] using h0
end Scott1976.DataTypesAsLattices
