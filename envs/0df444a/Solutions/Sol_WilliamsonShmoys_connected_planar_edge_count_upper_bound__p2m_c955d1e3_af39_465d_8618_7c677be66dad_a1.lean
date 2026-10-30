-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:45:05.250661+00:00
-- url     : https://prove2.me/submissions/45b166f4-7f95-43bb-a10a-2934869e9638

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_30506b39_3246_4bbb_be30_1654e491b341_a4

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hConn : M.Connected)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨N, hMN, hNDraw, hEdgeCountLe, hNCount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_30506b39_3246_4bbb_be30_1654e491b341_a4
      M hCard hM
  omega