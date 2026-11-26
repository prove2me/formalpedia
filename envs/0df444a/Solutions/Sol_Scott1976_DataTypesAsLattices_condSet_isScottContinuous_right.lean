-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.condSet_isScottContinuous_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:32.812304+00:00
-- url     : https://prove2.me/submissions/1f52daf0-247d-4cd0-8e2e-4bf3b59f7d26

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_pow2
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_zero
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
theorem _root_.solution (z x : Pomega) :
    IsScottContinuous (fun y => condSet z x y) := by
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with hzx | ⟨hky, ht⟩
    · refine mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hzx⟩
    · refine mem_scottUnion.mpr ⟨2 ^ k, by simp [e_pow2, Set.singleton_subset_iff, hky],
        Or.inr ⟨by simp [e_pow2], ht⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    rcases hkm with hzx | ⟨hky, ht⟩
    · exact Or.inl hzx
    · exact Or.inr ⟨hm hky, ht⟩
end Scott1976.DataTypesAsLattices
