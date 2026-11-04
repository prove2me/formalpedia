-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_0d510956_7da0_4290_84d6_372bf969c07f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:34:46.714241+00:00
-- url     : https://prove2.me/submissions/67c845e1-8e4c-47b1-8bf5-ce20183a480a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_of_connected_drawing__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_subgraph_of_extremal_planar_graph__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) (hconn : M.Connected) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  classical
  obtain ⟨N, hMN, hNconn, hNplanar, hNmax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph_of_connected_drawing__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
      M hV hM hconn
  have hNedges :=
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
      N hV hNplanar hNconn hNmax
  exact
    WilliamsonShmoys.edge_bound_of_subgraph_of_extremal_planar_graph__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
      M N hMN hNedges