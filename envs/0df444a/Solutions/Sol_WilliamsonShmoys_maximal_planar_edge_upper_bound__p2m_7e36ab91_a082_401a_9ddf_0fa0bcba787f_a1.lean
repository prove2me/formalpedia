-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_7e36ab91_a082_401a_9ddf_0fa0bcba787f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:30:28.494833+00:00
-- url     : https://prove2.me/submissions/582dcc98-dcc1-4684-9ada-d3f62da8bdb9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_6fae641e_69bd_437f_8912_51466427af04_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_6fae641e_69bd_437f_8912_51466427af04_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hsub, hcard, hconn, hdraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_6fae641e_69bd_437f_8912_51466427af04_a1
      G hG
  have hbound :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_6fae641e_69bd_437f_8912_51466427af04_a1
      H hV hconn hdraw
  omega