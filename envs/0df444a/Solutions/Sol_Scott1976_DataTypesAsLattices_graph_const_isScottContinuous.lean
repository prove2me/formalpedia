-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.graph_const_isScottContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:55:24.686032+00:00
-- url     : https://prove2.me/submissions/8fe1add3-1929-4b5e-9f04-26e476d07d77

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_isScottContinuous_monotone
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
theorem _root_.solution
    (g : Pomega → Pomega → Pomega)
    (hg : ∀ y, IsScottContinuous (fun x => g x y)) :
    IsScottContinuous (fun x => graph (fun y => g x y)) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨n, m, rfl, hm⟩
    have : m ∈ scottUnion (fun z => g z (e n)) x := by
      rw [← hg (e n) x]; exact hm
    obtain ⟨p, hp, hmp⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨p, hp, n, m, rfl, hmp⟩
  · intro hk
    obtain ⟨p, hp, n, m, rfl, hm⟩ := mem_scottUnion.mp hk
    exact ⟨n, m, rfl, isScottContinuous_monotone (hg (e n)) hp hm⟩
end Scott1976.DataTypesAsLattices
