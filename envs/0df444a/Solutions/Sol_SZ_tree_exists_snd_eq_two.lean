-- Prove2me | solution 1 for SZ.tree_exists_snd_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:28.195854+00:00
-- url     : https://prove2.me/submissions/5783ea4f-e680-4608-8f32-90f52c4ac15e

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_node_succ
import Theorems.Thm_SZ_g2_true_witness
import Theorems.Thm_SZ_tree_exists_branching

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) (N : ℕ) :
    ∃ k, N ≤ k ∧ (treeDigit β k).2 = 2 := by
  obtain ⟨k₁, hk₁N, hk₁⟩ := tree_exists_branching β N
  obtain ⟨k₂, hk₂, hk₂b⟩ := tree_exists_branching β (k₁ + 1)
  by_cases hd : (treeDigit β k₁).2 = 2
  · exact ⟨k₁, hk₁N, hd⟩
  · have hg : (node β (k₁ + 1)).g2 = false := by
      rw [node_succ, nodeNext, if_pos hk₁]
      show decide ((treeDigit β k₁).2 = 2) = false
      simp [hd]
    rcases g2_true_witness β hk₂ hk₂b.2.1 with h | ⟨i, hi1, hi2, hi3⟩
    · rw [hg] at h; exact absurd h (by simp)
    · exact ⟨i, by omega, hi3⟩
end SZ
