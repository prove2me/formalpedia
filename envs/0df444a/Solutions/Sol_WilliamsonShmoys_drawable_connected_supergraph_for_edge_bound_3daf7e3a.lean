-- Prove2me | solution 1 for WilliamsonShmoys.drawable_connected_supergraph_for_edge_bound_3daf7e3a
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:04:55.851516+00:00
-- url     : https://prove2.me/submissions/e6288677-e2ca-4ed9-ab39-15fae9b797f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_augmentation_of_strict_step
import Theorems.Thm_WilliamsonShmoys_drawable_disconnected_graph_has_strict_planar_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧ Q.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := by
  obtain ⟨Q, hPQ, hConn, hQdraw⟩ :=
    WilliamsonShmoys.finite_graph_augmentation_of_strict_step
      (D := WilliamsonShmoys.HasPlanarDrawingOn) P hPdraw
      (by
        intro G hGdraw hGnotConnected
        obtain ⟨R, hPR, hRdraw⟩ :=
          WilliamsonShmoys.drawable_disconnected_graph_has_strict_planar_extension
            G hGdraw hCard hGnotConnected
        exact ⟨R, hPR, hRdraw⟩)
  exact ⟨Q, hPQ, hConn, hQdraw⟩