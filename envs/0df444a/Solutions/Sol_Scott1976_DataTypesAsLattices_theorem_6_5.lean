-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_6_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:40.242465+00:00
-- url     : https://prove2.me/submissions/1287333a-beb4-4f13-b38f-19042d112427

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
theorem _root_.solution {f : Pomega → Pomega} (_hf : IsScottContinuous f)
    (a : Pomega) :
    {x | f x = a} = {x | a ⊆ f x} ∩ {x | f x ⊆ a} := by
  ext x
  constructor
  · intro hx
    have hfx : f x = a := hx
    change a ⊆ f x ∧ f x ⊆ a
    simp [hfx]
  · intro ⟨hle, hge⟩
    exact subset_antisymm hge hle
end Scott1976.DataTypesAsLattices
