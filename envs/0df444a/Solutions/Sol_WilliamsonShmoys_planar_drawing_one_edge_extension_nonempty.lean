-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_one_edge_extension_nonempty
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:53:19.055996+00:00
-- url     : https://prove2.me/submissions/6e9c40dd-4f92-4484-9897-564a73a3a58d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_vertices_not_reachable_card_ge_three
import Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_for_unreachable_vertices_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ K.Reachable u v ∧ H.Adj u v := by
  obtain ⟨u, v, huv⟩ :=
    WilliamsonShmoys.disconnected_vertices_not_reachable_card_ge_three
      K hCard hDisconnected
  obtain ⟨H, hKH, hH, hEdge⟩ :=
    WilliamsonShmoys.planar_drawing_bridge_for_unreachable_vertices_v2
      K hK u v huv
  exact ⟨H, hKH, hH, u, v, huv, hEdge⟩