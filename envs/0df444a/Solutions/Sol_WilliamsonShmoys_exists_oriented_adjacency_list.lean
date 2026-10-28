-- Prove2me | solution 1 for WilliamsonShmoys.exists_oriented_adjacency_list
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:39:07.895674+00:00
-- url     : https://prove2.me/submissions/3fd4befa-608e-4898-8901-d90c0e422e6b

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] (L : SimpleGraph V) :
    ∃ es : List (V × V),
      (∀ e ∈ es, L.Adj e.1 e.2) ∧
      es.length = 2 * L.edgeSet.ncard := by
  classical
  refine ⟨(Finset.univ : Finset L.Dart).toList.map (fun d => d.toProd), ?_, ?_⟩
  · intro e he
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 he
    exact d.adj
  · rw [List.length_map, Finset.length_toList, Finset.card_univ, SimpleGraph.dart_card_eq_twice_card_edges,
      ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
