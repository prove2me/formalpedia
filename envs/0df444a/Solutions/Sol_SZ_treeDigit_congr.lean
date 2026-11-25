-- Prove2me | solution 1 for SZ.treeDigit_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:49.874859+00:00
-- url     : https://prove2.me/submissions/9c39f591-8ad9-4e80-96e9-9a246185d1ff

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_node_used_succ_branch
import Theorems.Thm_SZ_node_used_mono
import Theorems.Thm_SZ_node_congr

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {β β' : ℕ → Bool} {n : ℕ} (hagree : ∀ i, i < n → β i = β' i)
    {k : ℕ} (hle : (node β (k + 1)).used ≤ n) : treeDigit β k = treeDigit β' k := by
  have hk : (node β k).used ≤ n := le_trans (node_used_mono β (Nat.le_succ k)) hle
  have heq : node β k = node β' k := node_congr hagree k hk
  rw [treeDigit, treeDigit, ← heq, nodeDigit, nodeDigit]
  by_cases hb : Branching (node β k)
  · rw [if_pos hb, if_pos hb]
    have hu : (node β k).used < n := by
      rw [node_used_succ_branch β hb] at hle; omega
    rw [hagree _ hu]
  · rw [if_neg hb, if_neg hb]
end SZ
