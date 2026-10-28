-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_a8cccb55
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:06:39.981836+00:00
-- url     : https://prove2.me/submissions/ae6550bb-1304-4abb-91e5-f2a1fc08bac7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_finite_graph_augmentation_from_one_step
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_components_a1fa2dac

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ H : SimpleGraph V,
      (W.edgeSet.ncard <= H.edgeSet.ncard /\
       H.Connected /\ WilliamsonShmoys.HasPlanarDrawingOn H) := by
  obtain ⟨H, hWH, hConn, hPlanar, hEdges⟩ :=
    WilliamsonShmoys.finite_graph_augmentation_from_one_step
      (V := V) (W := W) (P := WilliamsonShmoys.HasPlanarDrawingOn)
      hW
      (by
        intro G hWG hGPlanar hGDisconnected
        exact WilliamsonShmoys.planar_drawing_add_edge_between_components_a1fa2dac
          (V := V) G hGPlanar hGDisconnected)
  exact ⟨H, hEdges, hConn, hPlanar⟩