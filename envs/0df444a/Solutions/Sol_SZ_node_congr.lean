-- Prove2me | solution 1 for SZ.node_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:27:05.644419+00:00
-- url     : https://prove2.me/submissions/fd2bc627-75a9-4b6c-b2a0-e4553e10f83d

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_node_succ
import Theorems.Thm_SZ_node_used_succ_branch
import Theorems.Thm_SZ_node_used_mono

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {β β' : ℕ → Bool} {n : ℕ} (hagree : ∀ i, i < n → β i = β' i) :
    ∀ k, (node β k).used ≤ n → node β k = node β' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hle
    have hk : (node β k).used ≤ n := le_trans (node_used_mono β (Nat.le_succ k)) hle
    have heq : node β k = node β' k := ih hk
    rw [node_succ, node_succ, ← heq, nodeNext, nodeNext]
    by_cases hb : Branching (node β k)
    · rw [if_pos hb, if_pos hb]
      have hu : (node β k).used < n := by
        rw [node_used_succ_branch β hb] at hle; omega
      have hbit : β (node β k).used = β' (node β k).used := hagree _ hu
      simp only [nodeDigit, if_pos hb, hbit]
    · rw [if_neg hb, if_neg hb]
      simp only [nodeDigit, if_neg hb]
end SZ
