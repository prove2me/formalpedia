-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.eq_2_9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:25.095182+00:00
-- url     : https://prove2.me/submissions/0a503130-eea2-42a4-9121-c3c835995777

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
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
theorem _root_.solution (f g x : Pomega) :
    funOf (f ∪ g) x = funOf f x ∪ funOf g x := by
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    rcases hp with hp | hp
    · exact Or.inl ⟨n, hn, hp⟩
    · exact Or.inr ⟨n, hn, hp⟩
  · intro h
    rcases h with ⟨n, hn, hp⟩ | ⟨n, hn, hp⟩
    · exact ⟨n, hn, Or.inl hp⟩
    · exact ⟨n, hn, Or.inr hp⟩
end Scott1976.DataTypesAsLattices
