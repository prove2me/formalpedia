-- Prove2me | solution 1 for PHIP1887.sparse_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:01:49.359664+00:00
-- url     : https://prove2.me/submissions/2821a086-a7bd-4a56-9eec-0d3e2a93b941

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
import Theorems.Thm_PHIP1887_cofinal_positivity_excludes_seed
open MeasureTheory Set
open PHIP1887

theorem solution (H : Prop) (Q : ℕ → ℝ → ℝ) (S : Set ℕ)
    (hS : Cofinal S)
    (hforward : H → ∀ k ∈ S, PositiveAt Q k)
    (hentry : ¬H → ∃ K, 1 ≤ K ∧ NegativeAt Q K)
    (hstep : ∀ k, 1 ≤ k → NegativeAt Q k → NegativeAt Q (k+1)) :
    H ↔ ∀ k ∈ S, PositiveAt Q k := by
  constructor
  · exact hforward
  · intro hp
    by_contra hn
    exact cofinal_positivity_excludes_seed Q S hS hp hstep (hentry hn)
