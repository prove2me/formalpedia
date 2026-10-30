-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_connected_c61b3391
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:20:05.409433+00:00
-- url     : https://prove2.me/submissions/fb2e8772-06dc-48f3-ae69-b3eac212e62c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_triangulation_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hcard⟩ :=
    WilliamsonShmoys.planar_edge_count_triangulation_extension G hV hconn hG
  exact le_trans (Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH)) (le_of_eq hcard)