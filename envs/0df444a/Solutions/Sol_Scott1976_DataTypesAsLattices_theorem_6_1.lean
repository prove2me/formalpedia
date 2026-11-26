-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:01.013829+00:00
-- url     : https://prove2.me/submissions/3770cdb0-bdae-4db1-9358-abb7c56094a7

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Classification
import Theorems.Thm_Scott1976_DataTypesAsLattices_charOpen_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_isScottContinuous_monotone
import Theorems.Thm_Scott1976_DataTypesAsLattices_isScottOpen_isUpper
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_scottUnion


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution :
    (∀ f : Pomega → Pomega, IsScottContinuous f →
        IsScottOpen {x | 0 ∈ f x}) ∧
      (∀ U, IsScottOpen U →
        ∃ f, IsScottContinuous f ∧ U = {x | 0 ∈ f x}) := by
  constructor
  · intro f hf
    refine ⟨{n | 0 ∈ f (e n)}, ?_⟩
    ext x
    constructor
    · intro hx
      have : 0 ∈ scottUnion f x := by rwa [← hf x]
      obtain ⟨n, hn, h0⟩ := mem_scottUnion.mp this
      exact Set.mem_iUnion₂.mpr ⟨n, h0, hn⟩
    · intro hx
      obtain ⟨n, h0, hn⟩ := Set.mem_iUnion₂.mp hx
      exact isScottContinuous_monotone hf hn h0
  · intro U hU
    refine ⟨charOpen U, charOpen_isScottContinuous U, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨B, rfl⟩ := hU
      obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
      refine ⟨rfl, n, hxn, ?_⟩
      exact Set.mem_iUnion₂.mpr ⟨n, hn, (subset_rfl : e n ⊆ e n)⟩
    · intro ⟨_, n, hn, hne⟩
      exact isScottOpen_isUpper hU hne hn
end Scott1976.DataTypesAsLattices
