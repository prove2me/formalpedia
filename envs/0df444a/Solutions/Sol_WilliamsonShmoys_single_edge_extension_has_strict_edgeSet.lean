-- Prove2me | solution 1 for WilliamsonShmoys.single_edge_extension_has_strict_edgeSet
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T07:25:37.484712+00:00
-- url     : https://prove2.me/submissions/50e5acd9-247e-40fd-9d17-16a989b9ad62

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V)
    (u v : V)
    (hUV : ¬ K.Reachable u v)
    (hAdj : ∀ a b, L.Adj a b ↔ K.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    K.edgeSet ⊂ L.edgeSet := by
  have hle : K ≤ L := fun a b h => (hAdj a b).mpr (Or.inl h)
  have hne : K ≠ L := by
    intro e
    have : L.Adj u v := (hAdj u v).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    rw [← e] at this
    exact hUV this.reachable
  exact SimpleGraph.edgeSet_ssubset_edgeSet.mpr (lt_of_le_of_ne hle hne)
