-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.union_e_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:50.649815+00:00
-- url     : https://prove2.me/submissions/09a04f49-b99d-4196-95a7-0475b960472d

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_pow2
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (x : Pomega) : (⋃ n, eBelow x n) = x := by
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hke⟩ := Set.mem_iUnion.mp hk
    exact hn hke
  · intro hk
    refine Set.mem_iUnion.mpr ⟨2 ^ k, ?_⟩
    simp [eBelow, e_pow2, Set.singleton_subset_iff, hk]
end Scott1976.DataTypesAsLattices
