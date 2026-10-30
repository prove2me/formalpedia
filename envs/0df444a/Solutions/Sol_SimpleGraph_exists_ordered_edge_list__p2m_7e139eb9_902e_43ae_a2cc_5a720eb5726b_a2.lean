-- Prove2me | solution 1 for SimpleGraph.exists_ordered_edge_list__p2m_7e139eb9_902e_43ae_a2cc_5a720eb5726b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:22:42.140793+00:00
-- url     : https://prove2.me/submissions/7a2a621e-d620-4a42-8c33-f951fbe3b3f2

import Mathlib.Combinatorics.SimpleGraph.Operations

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    ∃ es : List (V × V),
      (∀ p, p ∈ es → p.1 < p.2 ∧ G.Adj p.1 p.2) ∧
      es.foldl (fun K p => K ⊔ SimpleGraph.edge p.1 p.2) ⊥ = G := by
  classical
  let es : List (V × V) :=
    (Finset.univ.filter fun p : V × V => p.1 < p.2 ∧ G.Adj p.1 p.2).toList
  have hprop : ∀ p, p ∈ es → p.1 < p.2 ∧ G.Adj p.1 p.2 := by
    intro p hp
    have hp' : p ∈ Finset.univ.filter
        (fun q : V × V => q.1 < q.2 ∧ G.Adj q.1 q.2) := by
      exact Finset.mem_toList.mp hp
    exact (Finset.mem_filter.mp hp').2
  have fold_adj (l : List (V × V)) :
      ∀ (K : SimpleGraph V) (x y : V),
        (l.foldl (fun H p => H ⊔ SimpleGraph.edge p.1 p.2) K).Adj x y ↔
          K.Adj x y ∨ ∃ p, p ∈ l ∧ (SimpleGraph.edge p.1 p.2).Adj x y := by
    induction l with
    | nil =>
        intro K x y
        simp
    | cons p l ih =>
        intro K x y
        rw [List.foldl_cons, ih]
        simp [SimpleGraph.sup_adj, List.mem_cons, or_assoc, and_left_comm, and_assoc, and_comm]
  refine ⟨es, hprop, ?_⟩
  ext x y
  change (es.foldl (fun K p => K ⊔ SimpleGraph.edge p.1 p.2) ⊥).Adj x y ↔ G.Adj x y
  rw [fold_adj]
  simp only [SimpleGraph.bot_adj, false_or]
  constructor
  · rintro ⟨p, hp, hEdge⟩
    obtain ⟨_, hpAdj⟩ := hprop p hp
    rcases (SimpleGraph.edge_adj p.1 p.2 x y).mp hEdge with ⟨hends, _⟩
    rcases hends with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · simpa [hx, hy] using hpAdj
    · simpa [hx, hy] using hpAdj.symm
  · intro hxy
    have hne : x ≠ y := hxy.ne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · refine ⟨(x, y), ?_, ?_⟩
      · change (x, y) ∈
          (Finset.univ.filter fun p : V × V => p.1 < p.2 ∧ G.Adj p.1 p.2).toList
        simp [hlt, hxy]
      · exact (SimpleGraph.edge_adj x y x y).mpr
          ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
    · refine ⟨(y, x), ?_, ?_⟩
      · change (y, x) ∈
          (Finset.univ.filter fun p : V × V => p.1 < p.2 ∧ G.Adj p.1 p.2).toList
        simp [hlt, hxy.symm]
      · exact (SimpleGraph.edge_adj y x x y).mpr
          ⟨Or.inr ⟨rfl, rfl⟩, hne⟩