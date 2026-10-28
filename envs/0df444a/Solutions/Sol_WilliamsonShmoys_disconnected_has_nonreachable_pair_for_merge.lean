-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_has_nonreachable_pair_for_merge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:34:43.116534+00:00
-- url     : https://prove2.me/submissions/20a7578d-5582-480f-b52a-6c679194a5ba

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by
  by_contra h
  push_neg at h
  have hne : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  exact hDisconnected ⟨fun u v => h u v⟩
