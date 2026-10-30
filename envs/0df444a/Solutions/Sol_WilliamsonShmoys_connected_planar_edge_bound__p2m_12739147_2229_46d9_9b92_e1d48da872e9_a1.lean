-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_12739147_2229_46d9_9b92_e1d48da872e9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:00:05.260218+00:00
-- url     : https://prove2.me/submissions/9a529670-46b3-4887-aadc-7d14d9627d2c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_drawable_edge_bound__p2m_2c5adea4_d505_4326_974e_37a0f04a34d9_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hSub : G ≤ H) (hConn : H.Connected)
    (hDraw : HasPlanarDrawingOn H) (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hEdges : G.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_mono hSub
  have hCardEdges : G.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono hEdges
  have hPlanar := WilliamsonShmoys.connected_drawable_edge_bound__p2m_2c5adea4_d505_4326_974e_37a0f04a34d9_a1
    H hConn hDraw hCard
  omega