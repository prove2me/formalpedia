-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_64c9133b_a623_45e5_bf52_4877372e6864_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:44:52.777299+00:00
-- url     : https://prove2.me/submissions/1e970e10-1047-4f58-aeb3-b66b96b28eab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_of_drawing__p2m_c95e5903_eb17_45df_8e19_128d3bfdea4d_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_c95e5903_eb17_45df_8e19_128d3bfdea4d_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    G.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨H, _hsub, hconn, hH, hmono⟩ :=
    WilliamsonShmoys.planar_connected_supergraph_of_drawing__p2m_c95e5903_eb17_45df_8e19_128d3bfdea4d_a1
      G hG (by omega)
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  exact hmono.trans
    (WilliamsonShmoys.connected_planar_edge_bound__p2m_c95e5903_eb17_45df_8e19_128d3bfdea4d_a1
      H hH hconn hcard)