-- Prove2me | solution 1 for WilliamsonShmoys.add_nonreachable_edge_graph__p2m_28fcd582_d200_46af_bf00_d4c58429d202_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T20:06:26.160755+00:00
-- url     : https://prove2.me/submissions/00784827-0e17-4980-b88d-fec6d2b867c0

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (u v : V)
    (huv : u < v ∧ ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ K.Reachable u v ∧
      (∀ x y, x < y →
        (K.Adj x y ↔ (G.Adj x y ∨ (x = u ∧ y = v)))) := by
  let K : SimpleGraph V :=
    { Adj := fun x y =>
        G.Adj x y ∨ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
      symm := by
        constructor
        intro x y h
        rcases h with hG | huv' | hvu'
        · exact Or.inl (@Std.Symm.symm V G.Adj G.symm x y hG)
        · exact Or.inr (Or.inr ⟨huv'.2, huv'.1⟩)
        · exact Or.inr (Or.inl ⟨hvu'.2, hvu'.1⟩)
      loopless := by
        constructor
        intro x h
        rcases h with hG | huv' | hvu'
        · exact @Std.Irrefl.irrefl V G.Adj G.loopless x hG
        · exact (ne_of_lt huv.1) (huv'.1.symm.trans huv'.2)
        · exact (ne_of_gt huv.1) (hvu'.1.symm.trans hvu'.2) }
  refine ⟨K, ?_, ?_, ?_⟩
  · intro x y hxy
    exact Or.inl hxy
  · exact (show K.Adj u v from Or.inr (Or.inl ⟨rfl, rfl⟩)).reachable
  · intro x y hxy
    change (G.Adj x y ∨ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) ↔
      (G.Adj x y ∨ (x = u ∧ y = v))
    constructor
    · intro h
      rcases h with hG | huv' | hvu'
      · exact Or.inl hG
      · exact Or.inr huv'
      · rcases hvu' with ⟨rfl, rfl⟩
        exact False.elim ((lt_asymm huv.1) hxy)
    · intro h
      rcases h with hG | huv'
      · exact Or.inl hG
      · exact Or.inr (Or.inl huv')