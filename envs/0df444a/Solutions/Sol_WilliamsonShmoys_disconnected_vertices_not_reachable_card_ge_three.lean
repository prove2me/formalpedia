-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_vertices_not_reachable_card_ge_three
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:39:39.790294+00:00
-- url     : https://prove2.me/submissions/abb99bad-6dcf-449c-884e-e77195cbf8b8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ u v : V, ¬ K.Reachable u v := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hp : ¬ K.Preconnected := fun h => hDisconnected ⟨h⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hp
  exact hp
