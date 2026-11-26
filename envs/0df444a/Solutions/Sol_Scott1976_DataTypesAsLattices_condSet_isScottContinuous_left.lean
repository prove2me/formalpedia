-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.condSet_isScottContinuous_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:05.925347+00:00
-- url     : https://prove2.me/submissions/5c26d651-942b-4fa8-8cfb-3087898cb9bc

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_one
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_pow2
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_scottUnion
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem


attribute [local simp] Scott1976.DataTypesAsLattices.mem_ofNat

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (x y : Pomega) :
    IsScottContinuous (fun z => condSet z x y) := by
  intro z
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hkx, h0⟩ | ⟨hky, ⟨t, ht⟩⟩
    · refine mem_scottUnion.mpr ⟨1, ?_, Or.inl ⟨hkx, ?_⟩⟩
      · simp [e_one, Set.singleton_subset_iff, h0]
      · simp [e_one]
    · refine mem_scottUnion.mpr ⟨2 ^ (t + 1), ?_, Or.inr ⟨hky, t, ?_⟩⟩
      · simp [e_pow2, Set.singleton_subset_iff, ht]
      · simp [e_pow2]
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    rcases hkm with ⟨hkx, h0⟩ | ⟨hky, ⟨t, ht⟩⟩
    · exact Or.inl ⟨hkx, hm h0⟩
    · exact Or.inr ⟨hky, t, hm ht⟩
end Scott1976.DataTypesAsLattices
