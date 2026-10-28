-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_bound_for_arbitrary_drawing_20261027_caef8af6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:31:09.584064+00:00
-- url     : https://prove2.me/submissions/fccc6704-89e0-443d-ba98-f5dff61f0102
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_euler_20261028
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound_euler_20261028
import Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeSet_ncard_mono_euler_20261028

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨G, hHG, hGConnected, hGDraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph_euler_20261028 H hV hDraw
  have hMono : H.edgeSet.ncard ≤ G.edgeSet.ncard :=
    WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono_euler_20261028 H G hHG
  have hBound : G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.connected_planar_edge_count_bound_euler_20261028 G hV hGConnected hGDraw
  omega