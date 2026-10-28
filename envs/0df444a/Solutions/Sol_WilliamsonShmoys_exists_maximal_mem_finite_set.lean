-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_mem_finite_set
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:06:23.584502+00:00
-- url     : https://prove2.me/submissions/96d4865a-f564-484f-94c3-81ab03762fbb

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Preorder α] (s : Set α) (hs : s.Finite)
    (hne : s.Nonempty) :
    ∃ a, a ∈ s ∧ ∀ b, b ∈ s → a ≤ b → b ≤ a := by
  classical
  revert hne
  refine Set.Finite.induction_on s hs ?_ ?_
  · intro hne
    simp at hne
  · intro x t hxt ht ih hne
    by_cases htn : t.Nonempty
    · obtain ⟨m, hm, hmax⟩ := ih htn
      by_cases hmx : m ≤ x
      · refine ⟨x, by simp, ?_⟩
        intro b hb hxb
        rcases Set.mem_insert_iff.mp hb with rfl | hb
        · exact le_rfl
        · exact le_trans (hmax b hb (le_trans hmx hxb)) hmx
      · refine ⟨m, by simp [hm], ?_⟩
        intro b hb hmb
        rcases Set.mem_insert_iff.mp hb with rfl | hb
        · exact False.elim (hmx hmb)
        · exact hmax b hb hmb
    · refine ⟨x, by simp, ?_⟩
      intro b hb hxb
      rcases Set.mem_insert_iff.mp hb with rfl | hb
      · exact le_rfl
      · exact False.elim (htn ⟨b, hb⟩)