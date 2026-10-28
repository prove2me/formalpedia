-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge_across_components
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:21:46.958752+00:00
-- url     : https://prove2.me/submissions/57d4d985-e1c1-45e2-8b28-4ee2ca159b53
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_IsPlanarDrawingData
import Definitions.Def_WilliamsonShmoys_HasFreeConnectingArc
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extend_free_arc
import Theorems.Thm_WilliamsonShmoys_disconnected_drawing_has_free_arc

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Adj u v ∧
      ∃ H : SimpleGraph V,
        G ≤ H ∧ H.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨u, v, hUnreachable, hNotAdj, p, arc, hDrawing, hFree⟩ :=
    WilliamsonShmoys.disconnected_drawing_has_free_arc G hG hDisconnected
  obtain ⟨H, hGH, hAdj, hPlanar⟩ :=
    WilliamsonShmoys.planar_drawing_extend_free_arc G p arc hDrawing
      u v hNotAdj hFree
  exact ⟨u, v, hNotAdj, H, hGH, hAdj, hPlanar⟩
