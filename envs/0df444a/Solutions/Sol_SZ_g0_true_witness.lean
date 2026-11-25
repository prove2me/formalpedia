-- Prove2me | solution 1 for SZ.g0_true_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:41.135859+00:00
-- url     : https://prove2.me/submissions/3f0cddd0-cfc5-4e56-b64f-eb99c8e50758

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_node_g0_succ

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) {j k : ℕ} (hjk : j ≤ k) (h : (node β k).g0 = true) :
    (node β j).g0 = true ∨ ∃ i, j ≤ i ∧ i < k ∧ (treeDigit β i).1 = 0 := by
  induction k, hjk using Nat.le_induction with
  | base => exact Or.inl h
  | succ k hk ih =>
    rcases node_g0_succ β k h with h' | h'
    · rcases ih h' with hx | ⟨i, hi1, hi2, hi3⟩
      · exact Or.inl hx
      · exact Or.inr ⟨i, hi1, by omega, hi3⟩
    · exact Or.inr ⟨k, hk, by omega, h'⟩
end SZ
