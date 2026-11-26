-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_1_2_i
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:14.539131+00:00
-- url     : https://prove2.me/submissions/897d8861-ee02-4b48-aa69-b4f72a4c704c

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Theorems.Thm_Scott1976_DataTypesAsLattices_isScottContinuous_monotone
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_scottUnion
import Theorems.Thm_Scott1976_DataTypesAsLattices_pair_inj


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf (graph f) = f := by
  funext x
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    obtain ⟨n', m', heq, hm'⟩ := hp
    obtain ⟨rfl, rfl⟩ := pair_inj heq
    exact isScottContinuous_monotone hf hn hm'
  · intro hm
    have : m ∈ scottUnion f x := by
      rw [← hf x]; exact hm
    obtain ⟨n, hn, hmn⟩ := mem_scottUnion.mp this
    exact ⟨n, hn, ⟨n, m, rfl, hmn⟩⟩
end Scott1976.DataTypesAsLattices
