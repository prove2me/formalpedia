-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.exists_e_cover_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:55:32.232899+00:00
-- url     : https://prove2.me/submissions/9232d86e-0459-4407-8f69-bbf82eaeb53c

import Mathlib.Topology.Order
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_isScottContinuous_monotone
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_or
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_or_of_subset
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_zero
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem



set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {x : Pomega} (s : Finset ℕ)
    (h : ∀ k ∈ s, ∃ n, e n ⊆ x ∧ k ∈ f (e n)) :
    ∃ N, e N ⊆ x ∧ (s : Set ℕ) ⊆ f (e N) := by
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp [e_zero], by simp⟩
  | insert k s hks ih =>
    obtain ⟨N, hN, hs⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨n, hn, hk⟩ := h k (Finset.mem_insert_self _ _)
    refine ⟨n ||| N, e_or_of_subset hn hN, ?_⟩
    intro j hj
    rw [Finset.coe_insert, Set.mem_insert_iff] at hj
    rcases hj with rfl | hj
    · have : e n ⊆ e (n ||| N) := by rw [e_or]; exact Set.subset_union_left
      exact isScottContinuous_monotone hf this hk
    · have : e N ⊆ e (n ||| N) := by rw [e_or]; exact Set.subset_union_right
      exact isScottContinuous_monotone hf this (hs hj)
end Scott1976.DataTypesAsLattices
