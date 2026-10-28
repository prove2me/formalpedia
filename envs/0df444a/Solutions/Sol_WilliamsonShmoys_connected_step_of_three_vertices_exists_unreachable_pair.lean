-- Prove2me | solution 1 for WilliamsonShmoys.connected_step_of_three_vertices_exists_unreachable_pair
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T10:18:56.898259+00:00
-- url     : https://prove2.me/submissions/6f2d6433-71ab-45f1-94ad-5c7572fe8687

import Mathlib
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by
  by_contra h
  push_neg at h
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact hDisconnected ⟨h⟩
