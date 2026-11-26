-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.gfpBelow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:19.978146+00:00
-- url     : https://prove2.me/submissions/98ae0253-1bf2-422b-a418-c4d5628b3c68

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Theorems.Thm_Scott1976_DataTypesAsLattices_isScottContinuous_monotone
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_scottUnion
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_ofNat
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem



set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega} (hf : IsScottContinuous f) (b : Pomega)
    (_hb : f b ⊆ b) : gfpBelow f b ⊆ b := by
  have hg : IsScottContinuous (fun z => f z ∩ b) := by
    intro x
    ext k
    constructor
    · intro ⟨hkf, hkb⟩
      have : k ∈ scottUnion f x := by rwa [← hf x]
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨n, hn, hkn, hkb⟩
    · intro hk
      obtain ⟨n, hn, hkn, hkb⟩ := mem_scottUnion.mp hk
      exact ⟨isScottContinuous_monotone hf hn hkn, hkb⟩
  have hpre : (fun z => f z ∩ b) b ⊆ b := Set.inter_subset_right
  -- iterates stay below `b`
  have hiter : ∀ n, iterateBot (fun z => f z ∩ b) n ⊆ b := by
    intro n
    induction n with
    | zero => simp [iterateBot, botElem]
    | succ n ih =>
      intro k hk
      simp [iterateBot] at hk
      exact hk.2
  intro k hk
  obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
  exact hiter n hkn
end Scott1976.DataTypesAsLattices
