-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.funOf_isScottContinuous_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:55:25.149241+00:00
-- url     : https://prove2.me/submissions/f75988b5-5517-4284-acd1-e5cba816a993

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
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
theorem _root_.solution (y : Pomega) :
    IsScottContinuous (fun u => funOf u y) := by
  intro u
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    refine mem_scottUnion.mpr ⟨2 ^ pair n m, ?_, ⟨n, hn, ?_⟩⟩
    · simp [e_pow2, Set.singleton_subset_iff, hp]
    · simp [e_pow2]
  · intro hm
    obtain ⟨k, hk, n, hn, hp⟩ := mem_scottUnion.mp hm
    exact ⟨n, hn, hk hp⟩
end Scott1976.DataTypesAsLattices
