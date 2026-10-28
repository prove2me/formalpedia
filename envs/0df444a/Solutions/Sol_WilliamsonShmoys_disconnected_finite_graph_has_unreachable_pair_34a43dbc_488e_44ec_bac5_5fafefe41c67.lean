-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_finite_graph_has_unreachable_pair_34a43dbc_488e_44ec_bac5_5fafefe41c67
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T03:10:11.980948+00:00
-- url     : https://prove2.me/submissions/0a4ae852-3b6d-455b-aa67-e93ed5262950

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ u v : V, ¬ K.Reachable u v := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hp : ¬ K.Preconnected := fun h => hDisconnected ⟨h⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hp
  exact hp
