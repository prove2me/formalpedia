-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_6_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:39.748427+00:00
-- url     : https://prove2.me/submissions/a54c84c5-f94d-464e-80c0-be4ac423d829

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
theorem _root_.solution {f g : Pomega → Pomega}
    (_hf : IsScottContinuous f) (_hg : IsScottContinuous g) :
    {x | f x = g x} =
      ⋂ n, ({x | n ∈ f x ∧ n ∈ g x} ∪ {x | n ∉ f x ∧ n ∉ g x}) := by
  ext x
  constructor
  · intro h
    refine Set.mem_iInter.mpr fun n => ?_
    have heq : f x = g x := h
    by_cases hn : n ∈ f x
    · exact Or.inl ⟨hn, by rwa [← heq]⟩
    · exact Or.inr ⟨hn, by simpa [heq] using hn⟩
  · intro hx
    ext n
    have hn := Set.mem_iInter.mp hx n
    constructor
    · intro hfx
      rcases hn with ⟨_, hng⟩ | ⟨hnf, _⟩
      · exact hng
      · exact (hnf hfx).elim
    · intro hgx
      rcases hn with ⟨hnf, _⟩ | ⟨_, hng⟩
      · exact hnf
      · exact (hng hgx).elim
end Scott1976.DataTypesAsLattices
