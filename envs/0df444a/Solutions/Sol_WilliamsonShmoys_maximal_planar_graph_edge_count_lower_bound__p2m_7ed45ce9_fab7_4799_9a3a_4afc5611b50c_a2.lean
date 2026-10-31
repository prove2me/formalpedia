-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound__p2m_7ed45ce9_fab7_4799_9a3a_4afc5611b50c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:53:56.977641+00:00
-- url     : https://prove2.me/submissions/4dee80ee-b03d-41c8-80cd-29e9be083e30

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_edge_count__p2m_1cec101a_a7da_4edb_96e9_a9cac5943fca_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hDraw : HasPlanarDrawingOn N)
    (hV : 3 <= Fintype.card V)
    (hMax : forall P : SimpleGraph V, N <= P -> HasPlanarDrawingOn P -> P = N) :
    3 * Fintype.card V <= N.edgeSet.ncard + 6 := by
  have hc :=
    WilliamsonShmoys.planar_supergraph_triangulation_edge_count__p2m_1cec101a_a7da_4edb_96e9_a9cac5943fca_a1
      N hDraw hV
  let P : SimpleGraph V := Classical.choose hc
  have hP := Classical.choose_spec hc
  have hNP : N <= P := hP.1
  have hPD : HasPlanarDrawingOn P := hP.2.1
  have hEdges : P.edgeSet.ncard + 6 = 3 * Fintype.card V := hP.2.2
  have hPN : P = N := hMax P hNP hPD
  have hCount : P.edgeSet.ncard = N.edgeSet.ncard :=
    congrArg (fun G : SimpleGraph V => G.edgeSet.ncard) hPN
  omega