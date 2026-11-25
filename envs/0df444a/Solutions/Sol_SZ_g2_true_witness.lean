-- Prove2me | solution 1 for SZ.g2_true_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:54.060853+00:00
-- url     : https://prove2.me/submissions/1041d201-ca3d-4dd4-81ae-295f9413a344

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_node_g2_succ

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) {j k : ℕ} (hjk : j ≤ k) (h : (node β k).g2 = true) :
    (node β j).g2 = true ∨ ∃ i, j ≤ i ∧ i < k ∧ (treeDigit β i).2 = 2 := by
  induction k, hjk using Nat.le_induction with
  | base => exact Or.inl h
  | succ k hk ih =>
    rcases node_g2_succ β k h with h' | h'
    · rcases ih h' with hx | ⟨i, hi1, hi2, hi3⟩
      · exact Or.inl hx
      · exact Or.inr ⟨i, hi1, by omega, hi3⟩
    · exact Or.inr ⟨k, hk, by omega, h'⟩
end SZ
