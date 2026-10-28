-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_add_edge_across_components
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:20:07.824229+00:00
-- url     : https://prove2.me/submissions/72960379-e6f8-4c5b-97d8-31d5b612df36
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_has_connected_supergraph_extension
import Theorems.Thm_WilliamsonShmoys_connected_extension_adds_intercomponent_edge

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hNotConnected : ¬ J.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ J.Adj u v ∧
      ∃ K : SimpleGraph V,
        J ≤ K ∧ K.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  obtain ⟨M, hJM, hMDraw, hMConnected⟩ :=
    WilliamsonShmoys.planarDrawingOn_has_connected_supergraph_extension J hDraw
  obtain ⟨u, v, huv, hnot, hMuv⟩ :=
    WilliamsonShmoys.connected_extension_adds_intercomponent_edge J M hJM
      hMConnected hNotConnected
  exact ⟨u, v, huv, hnot, M, hJM, hMuv, hMDraw⟩