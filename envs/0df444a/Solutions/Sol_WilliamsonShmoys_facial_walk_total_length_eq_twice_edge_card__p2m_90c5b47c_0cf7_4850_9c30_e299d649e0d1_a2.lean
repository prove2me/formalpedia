-- Prove2me | solution 1 for WilliamsonShmoys.facial_walk_total_length_eq_twice_edge_card__p2m_90c5b47c_0cf7_4850_9c30_e299d649e0d1_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:56:40.484992+00:00
-- url     : https://prove2.me/submissions/47a8427a-ee4d-4427-8c47-b196c0098f9f

import Mathlib
set_option autoImplicit false

private theorem length_eq_sum_count {α : Type} [Fintype α] [DecidableEq α]
    [BEq α] [LawfulBEq α] (l : List α) :
    l.length = ∑ a : α, l.count a := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp [List.count_cons, ih, Finset.sum_add_distrib]

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj) (k : ℕ)
    (faces : Fin k → List (V × V))
    (hcount : (letI : DecidableRel G.Adj := dG; ∀ u v,
      (List.flatten (List.ofFn faces)).count (u, v) =
        if G.Adj u v then 1 else 0)) :
    (List.flatten (List.ofFn faces)).length =
      2 * (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) := by
  letI : DecidableRel G.Adj := dG
  let l := List.flatten (List.ofFn faces)
  calc
    l.length = ∑ p : V × V, l.count p := length_eq_sum_count l
    _ = ∑ p : V × V, (if G.Adj p.1 p.2 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hcount p.1 p.2
    _ = ∑ v : V, G.degree v := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro v hv
      simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
    _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges