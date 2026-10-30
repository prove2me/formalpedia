-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_d5ec0378_40af_49f0_96a5_235e13fa397b_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:55:27.201139+00:00
-- url     : https://prove2.me/submissions/170782a7-6839-4966-b69d-dfd3a0253f36
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph__p2m_09553c75_05d3_4866_a115_40c42a94c393_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_09553c75_05d3_4866_a115_40c42a94c393_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    U.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hConnected, hSubgraph, hDrawing, hCard⟩ :=
    WilliamsonShmoys.planar_connected_supergraph__p2m_09553c75_05d3_4866_a115_40c42a94c393_a2
      U hV hU
  have hConnectedBound :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_09553c75_05d3_4866_a115_40c42a94c393_a2
      H hV hConnected hDrawing
  omega