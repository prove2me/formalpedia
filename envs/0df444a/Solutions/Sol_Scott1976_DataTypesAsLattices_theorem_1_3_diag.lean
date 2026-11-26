-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_1_3_diag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:54:29.566065+00:00
-- url     : https://prove2.me/submissions/f42c7b7d-b92b-47dd-b822-59bac9914073

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_or
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_or_of_subset
import Theorems.Thm_Scott1976_DataTypesAsLattices_isScottContinuous_monotone
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_scottUnion


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega → Pomega}
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y))
    {x : Pomega} :
    f x x = ⋃ n, {k | e n ⊆ x ∧ k ∈ f (e n) (e n)} := by
  apply subset_antisymm
  · intro k hk
    have : k ∈ scottUnion (fun z => f z x) x := by
      rw [← hfx x x]; exact hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
    have : k ∈ scottUnion (fun y => f (e n) y) x := by
      rw [← hfy (e n) x]; exact hkn
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp this
    refine Set.mem_iUnion.mpr ⟨n ||| m, ?_⟩
    refine ⟨e_or_of_subset hn hm, ?_⟩
    have hle : e n ⊆ e (n ||| m) := by rw [e_or]; exact Set.subset_union_left
    have hre : e m ⊆ e (n ||| m) := by rw [e_or]; exact Set.subset_union_right
    exact isScottContinuous_monotone (hfy (e (n ||| m))) hre
      (isScottContinuous_monotone (hfx (e m)) hle hkm)
  · intro k hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion.mp hk
    exact isScottContinuous_monotone (hfy x) hn
      (isScottContinuous_monotone (hfx (e n)) hn hkn)
end Scott1976.DataTypesAsLattices
