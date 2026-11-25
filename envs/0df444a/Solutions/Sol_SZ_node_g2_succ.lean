-- Prove2me | solution 1 for SZ.node_g2_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:55:16.155888+00:00
-- url     : https://prove2.me/submissions/83bfa6e8-a66c-4a22-99e5-bfc981262623

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
    (node β (k + 1)).g2 = true → (node β k).g2 = true ∨ (treeDigit β k).2 = 2 := by
  rw [node_succ, nodeNext]
  split_ifs with hb <;> simp only [treeDigit] <;> intro h
  · exact Or.inr (of_decide_eq_true h)
  · rcases Bool.or_eq_true_iff.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (of_decide_eq_true h')
end SZ
