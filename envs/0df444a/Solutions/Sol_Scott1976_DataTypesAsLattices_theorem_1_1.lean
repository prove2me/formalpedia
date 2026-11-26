-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:39.222224+00:00
-- url     : https://prove2.me/submissions/d3ffc5f6-cc6d-4c8f-b66c-8f050c3cb065

import Mathlib.Topology.Order
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_scottUnion
import Theorems.Thm_Scott1976_DataTypesAsLattices_isScottContinuous_monotone
import Theorems.Thm_Scott1976_DataTypesAsLattices_exists_e_cover_finite
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_finite
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_pow2
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem



set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (f : Pomega → Pomega) :
    IsScottContinuous f ↔
      ∀ x m, e m ⊆ f x ↔ ∃ n, e n ⊆ x ∧ e m ⊆ f (e n) := by
  constructor
  · intro hf x m
    constructor
    · intro hmf
      have : ∀ k ∈ e m, ∃ n, e n ⊆ x ∧ k ∈ f (e n) := by
        intro k hk
        have : k ∈ scottUnion f x := by
          rw [← hf x]; exact hmf hk
        exact mem_scottUnion.mp this
      obtain ⟨s, hs⟩ := (e_finite m).exists_finset_coe
      obtain ⟨N, hN, hsf⟩ := exists_e_cover_finite hf s (fun k hk =>
        this k (by
          have : k ∈ (s : Set ℕ) := hk
          rwa [hs] at this))
      exact ⟨N, hN, by simpa [hs] using hsf⟩
    · intro ⟨n, hn, hmf⟩
      exact subset_trans hmf (isScottContinuous_monotone hf hn)
  · intro h x
    ext k
    constructor
    · intro hk
      have : e (2 ^ k) ⊆ f x := by
        simp [e_pow2, Set.singleton_subset_iff, hk]
      obtain ⟨n, hn, hkn⟩ := (h x (2 ^ k)).mp this
      refine mem_scottUnion.mpr ⟨n, hn, ?_⟩
      simpa [e_pow2, Set.singleton_subset_iff] using hkn
    · intro hk
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
      have : e (2 ^ k) ⊆ f (e n) := by
        simp [e_pow2, Set.singleton_subset_iff, hkn]
      have : e (2 ^ k) ⊆ f x := (h x (2 ^ k)).mpr ⟨n, hn, this⟩
      simpa [e_pow2, Set.singleton_subset_iff] using this
end Scott1976.DataTypesAsLattices
