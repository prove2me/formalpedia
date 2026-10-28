-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_upper_bound_12627fe4_bb8b_4611_a4bf_2ba10834172b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:59:40.446794+00:00
-- url     : https://prove2.me/submissions/d269e67e-97c0-4b50-8e2e-d8297e4acabb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_bound_v2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_component_join_v2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hSub, hConnected, hDraw⟩ :=
    WilliamsonShmoys.planar_drawing_component_join_v2 L hLdraw hCard
  have hBound :=
    WilliamsonShmoys.connected_planar_drawing_euler_bound_v2 H hDraw hConnected hCard
  have hEdges : L.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono hSub
  omega