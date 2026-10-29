-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_bound_e51c1790
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T05:14:03.470751+00:00
-- url     : https://prove2.me/submissions/38b6659b-8d5a-4e5c-a366-e9fce4147277
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_repair__p2m_21446003_fac0_46fd_be6f_03d17c7cc1aa_a4
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_repair__p2m_21446003_fac0_46fd_be6f_03d17c7cc1aa_a4
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    U.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hEdges, hConnected, hPlanar⟩ :=
    WilliamsonShmoys.planar_connected_supergraph_repair__p2m_21446003_fac0_46fd_be6f_03d17c7cc1aa_a4 U hV hU
  have hBound :=
    WilliamsonShmoys.connected_planar_edge_bound_repair__p2m_21446003_fac0_46fd_be6f_03d17c7cc1aa_a4 H hV hConnected hPlanar
  omega
