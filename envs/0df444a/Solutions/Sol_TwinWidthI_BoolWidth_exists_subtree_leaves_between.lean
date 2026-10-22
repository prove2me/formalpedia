-- Prove2me | solution 1 for TwinWidthI.BoolWidth.exists_subtree_leaves_between
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:37:07.857851+00:00
-- url     : https://prove2.me/submissions/e1452fd7-cf5d-4475-96b8-2594bd76b333

import Mathlib
import Definitions.Def_TwinWidthI_BoolWidth_Setting

set_option autoImplicit false
open Finset TwinWidthI.BoolWidth

theorem X_self_mem_subtrees {α : Type*} (T : DTree α) : T ∈ T.subtrees := by
  cases T <;> simp [DTree.subtrees]

theorem X_proper_sub {α : Type*} (T : DTree α) : ∀ S ∈ T.properSubtrees, S ∈ T.subtrees := by
  intro S hS
  cases T with
  | leaf a => simp [DTree.properSubtrees] at hS
  | node l r =>
    simp only [DTree.properSubtrees] at hS
    simp only [DTree.subtrees]
    exact List.mem_cons_of_mem _ hS

theorem solution {α : Type*} (T : DTree α) (N : ℕ) (hN : 1 ≤ N)
    (hT : 2 * N < T.leaves.length) :
    ∃ S ∈ T.properSubtrees, N + 1 ≤ S.leaves.length ∧ S.leaves.length ≤ 2 * N := by
  induction T with
  | leaf a => simp [DTree.leaves] at hT; omega
  | node l r ihl ihr =>
    simp only [DTree.leaves, List.length_append] at hT
    by_cases hl : 2 * N < l.leaves.length
    · obtain ⟨S, hS, h⟩ := ihl hl
      refine ⟨S, ?_, h⟩
      simp only [DTree.properSubtrees, List.mem_append]
      exact Or.inl (X_proper_sub l S hS)
    by_cases hr : 2 * N < r.leaves.length
    · obtain ⟨S, hS, h⟩ := ihr hr
      refine ⟨S, ?_, h⟩
      simp only [DTree.properSubtrees, List.mem_append]
      exact Or.inr (X_proper_sub r S hS)
    by_cases hl' : N + 1 ≤ l.leaves.length
    · refine ⟨l, ?_, hl', by omega⟩
      simp only [DTree.properSubtrees, List.mem_append]
      exact Or.inl (X_self_mem_subtrees l)
    · refine ⟨r, ?_, by omega, by omega⟩
      simp only [DTree.properSubtrees, List.mem_append]
      exact Or.inr (X_self_mem_subtrees r)
