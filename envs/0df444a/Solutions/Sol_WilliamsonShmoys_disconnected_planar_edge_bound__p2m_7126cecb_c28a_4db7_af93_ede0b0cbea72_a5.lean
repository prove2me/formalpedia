-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_edge_bound__p2m_7126cecb_c28a_4db7_af93_ede0b0cbea72_a5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T13:02:52.778347+00:00
-- url     : https://prove2.me/submissions/eac60a66-91e5-43d4-a2a0-072a17a53c90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_093d3833_026f_4cc9_9066_8ef7487e85b6_a2
import Theorems.Thm_WilliamsonShmoys_connected_supergraph_of_disconnected_planar__p2m_093d3833_026f_4cc9_9066_8ef7487e85b6_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hdis : ¬ G.Connected) :
    G.edgeSet.ncard + 7 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hsub, hconn, hplan, hgain⟩ :=
    WilliamsonShmoys.connected_supergraph_of_disconnected_planar__p2m_093d3833_026f_4cc9_9066_8ef7487e85b6_a2
      G hG hV hdis
  have hb :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_093d3833_026f_4cc9_9066_8ef7487e85b6_a2
      H hplan hV hconn
  omega