-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_1_3_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:17.935729+00:00
-- url     : https://prove2.me/submissions/950a170c-10c8-43f0-8abe-5a9991f1bcd0

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_pow2
import Theorems.Thm_Scott1976_DataTypesAsLattices_isScottContinuous_monotone
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_scottUnion
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_1
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem



set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (f ∘ g) := by
  intro x
  ext k
  constructor
  · intro hk
    have hk' : k ∈ f (g x) := hk
    have := (theorem_1_1 f).mp hf (g x) (2 ^ k)
    have hfin : e (2 ^ k) ⊆ f (g x) := by
      simpa [e_pow2, Set.singleton_subset_iff] using hk'
    obtain ⟨m, hm, hkm⟩ := this.mp hfin
    have := (theorem_1_1 g).mp hg x m
    obtain ⟨n, hn, hmn⟩ := this.mp hm
    refine mem_scottUnion.mpr ⟨n, hn, ?_⟩
    have : e (2 ^ k) ⊆ f (g (e n)) :=
      subset_trans hkm (isScottContinuous_monotone hf hmn)
    simpa [e_pow2, Set.singleton_subset_iff] using this
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    exact isScottContinuous_monotone hf (isScottContinuous_monotone hg hn) hkn
end Scott1976.DataTypesAsLattices
