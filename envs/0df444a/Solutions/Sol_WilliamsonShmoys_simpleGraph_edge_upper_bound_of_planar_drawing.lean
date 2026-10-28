-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_edge_upper_bound_of_planar_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:17:46.951682+00:00
-- url     : https://prove2.me/submissions/7eb7a3b8-fee0-454d-91d6-256750b3c2dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_connected_supergraph
import Theorems.Thm_WilliamsonShmoys_simpleGraph_edge_upper_bound_of_connected_planar_drawing

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKConnected, hKDrawing⟩ :=
    WilliamsonShmoys.planar_drawing_has_connected_supergraph H hH hCard
  have hKBound :=
    WilliamsonShmoys.simpleGraph_edge_upper_bound_of_connected_planar_drawing
      K hKConnected hKDrawing hCard
  have hMono : H.edgeSet.ncard ≤ K.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hHK)
  omega