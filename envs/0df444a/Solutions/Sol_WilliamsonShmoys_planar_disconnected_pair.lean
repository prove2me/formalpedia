-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_pair
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:43:39.6702+00:00
-- url     : https://prove2.me/submissions/837a38d8-da43-4aad-8273-369dc8230c3d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ P.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ P.Adj u v ∧ ¬ P.Reachable u v := by
  have hne : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  have hnp : ¬ P.Preconnected := fun h => hDisconnected ⟨h⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hnp
  obtain ⟨u, v, huv⟩ := hnp
  exact ⟨u, v, fun h => huv (h ▸ SimpleGraph.Reachable.refl u), fun h => huv h.reachable, huv⟩
