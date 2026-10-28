-- Prove2me | solution 1 for WilliamsonShmoys.add_edge_strict_of_unreachable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:29:32.716992+00:00
-- url     : https://prove2.me/submissions/0dc5d22f-63ee-4847-8b61-1b2058f901b9

import Mathlib
theorem solution
    {V : Type} [LinearOrder V]
    (G : SimpleGraph V)
    {u v : V}
    (huv : u < v)
    (hUnreachable : ¬ G.Reachable u v) :
    G < G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v) := by
  refine lt_of_le_of_ne le_sup_left fun h => hUnreachable ?_
  have hadj : (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)).Adj u v := by
    right
    exact ⟨huv.ne, Or.inl ⟨rfl, rfl⟩⟩
  rw [← h] at hadj
  exact hadj.reachable
