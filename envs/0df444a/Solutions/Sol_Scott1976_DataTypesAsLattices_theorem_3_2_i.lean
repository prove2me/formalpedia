-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_3_2_i
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:50.571235+00:00
-- url     : https://prove2.me/submissions/1e3df844-d641-41e8-b8ba-6bb3cb21879b

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
theorem _root_.solution : condSet (ofNat 0) Gcomb botElem = Gcomb := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨hG, _⟩ | ⟨_, ⟨k, hk⟩⟩
    · exact hG
    · simp [ofNat] at hk
  · intro hG
    exact Or.inl ⟨hG, rfl⟩
end Scott1976.DataTypesAsLattices
