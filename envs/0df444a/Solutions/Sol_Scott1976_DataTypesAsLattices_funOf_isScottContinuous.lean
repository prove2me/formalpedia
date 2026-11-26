-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.funOf_isScottContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:43.120088+00:00
-- url     : https://prove2.me/submissions/dd174e23-3aad-42d1-b2d7-5b941c1e51a6

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_scottUnion


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (u : Pomega) : IsScottContinuous (funOf u) := by
  intro x
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    exact mem_scottUnion.mpr ⟨n, hn, ⟨n, subset_rfl, hp⟩⟩
  · intro hm
    obtain ⟨n, hn, ⟨k, hk, hp⟩⟩ := mem_scottUnion.mp hm
    exact ⟨k, subset_trans hk hn, hp⟩
end Scott1976.DataTypesAsLattices
