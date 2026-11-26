-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.exists_index_of_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:32.235945+00:00
-- url     : https://prove2.me/submissions/9fbbef33-b3aa-4970-994a-7787c2f70436

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Theorems.Thm_Scott1976_DataTypesAsLattices_chain_mono
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem



set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (xs : ℕ → Pomega)
    (hmono : ∀ n, xs n ⊆ xs (n + 1))
    (s : Finset ℕ) (h : ∀ k ∈ s, ∃ n, k ∈ xs n) :
    ∃ N, (s : Set ℕ) ⊆ xs N := by
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | insert i t hit ih =>
    obtain ⟨N, hN⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨Ni, hNi⟩ := h i (Finset.mem_insert_self _ _)
    refine ⟨max N Ni, ?_⟩
    intro j hj
    rw [Finset.coe_insert, Set.mem_insert_iff] at hj
    rcases hj with rfl | hj
    · exact chain_mono xs hmono Ni (max N Ni) (le_max_right _ _) hNi
    · exact chain_mono xs hmono N (max N Ni) (le_max_left _ _) (hN hj)
end Scott1976.DataTypesAsLattices
