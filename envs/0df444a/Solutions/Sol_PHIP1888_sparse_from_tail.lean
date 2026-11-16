-- Prove2me | solution 1 for PHIP1888.sparse_from_tail
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:04:03.038858+00:00
-- url     : https://prove2.me/submissions/1de1876a-b516-4592-b38c-3f72d5ac2a30

import Mathlib
open MeasureTheory Set

theorem solution (H : Prop) (Pos Neg : Nat → Prop) (S : Nat → Prop)
    (hexcl : ∀ k, Pos k → ¬ Neg k)
    (hS : ∀ K, ∃ k, S k ∧ K ≤ k)
    (hforward : H → ∀ k, S k → Pos k)
    (htail : ¬ H → ∃ K, ∀ k, K ≤ k → Neg k) :
    H ↔ ∀ k, S k → Pos k := by
  constructor
  · exact hforward
  · intro hp
    apply Classical.byContradiction
    intro hn
    obtain ⟨K, hK⟩ := htail hn
    obtain ⟨k, hkS, hKk⟩ := hS K
    exact hexcl k (hp k hkS) (hK k hKk)
