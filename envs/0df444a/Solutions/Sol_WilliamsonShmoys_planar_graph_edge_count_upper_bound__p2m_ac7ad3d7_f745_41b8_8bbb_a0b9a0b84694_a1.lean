-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_ac7ad3d7_f745_41b8_8bbb_a0b9a0b84694_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:15:25.978205+00:00
-- url     : https://prove2.me/submissions/f27772e8-f6a0-48c1-be90-8ef1e3b01534
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_f8136575_362d_4cf6_b5f8_07670116a17a_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper_bound__p2m_f8136575_362d_4cf6_b5f8_07670116a17a_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hsub, hconn, hHplanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_f8136575_362d_4cf6_b5f8_07670116a17a_a1
      G hplanar
  exact (Set.ncard_mono hsub).trans
    (WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_f8136575_362d_4cf6_b5f8_07670116a17a_a1
      H hHplanar hconn hcard)