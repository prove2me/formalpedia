-- Prove2me | solution 1 for SZ.node_used_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:29.898091+00:00
-- url     : https://prove2.me/submissions/ffb2a39e-b509-4459-bc0c-ca3c0b07b6ed

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_tree_exists_branching
import Theorems.Thm_SZ_node_used_succ_branch
import Theorems.Thm_SZ_node_used_mono

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) (n : ℕ) : ∃ k, n < (node β k).used := by
  induction n with
  | zero =>
    obtain ⟨k, -, hk⟩ := tree_exists_branching β 0
    exact ⟨k + 1, by rw [node_used_succ_branch β hk]; omega⟩
  | succ n ih =>
    obtain ⟨K, hK⟩ := ih
    obtain ⟨k, hkK, hk⟩ := tree_exists_branching β K
    have := node_used_mono β hkK
    exact ⟨k + 1, by rw [node_used_succ_branch β hk]; omega⟩
end SZ
