-- Prove2me | solution 1 for SZ.node_g0_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:55:11.145039+00:00
-- url     : https://prove2.me/submissions/05949f3c-d96e-4750-95b5-7a8ed3e631e7

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_node_succ

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) (k : ℕ) :
    (node β (k + 1)).g0 = true → (node β k).g0 = true ∨ (treeDigit β k).1 = 0 := by
  rw [node_succ, nodeNext]
  split_ifs with hb <;> simp only [treeDigit] <;> intro h
  · exact Or.inr (of_decide_eq_true h)
  · rcases Bool.or_eq_true_iff.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (of_decide_eq_true h')
end SZ
