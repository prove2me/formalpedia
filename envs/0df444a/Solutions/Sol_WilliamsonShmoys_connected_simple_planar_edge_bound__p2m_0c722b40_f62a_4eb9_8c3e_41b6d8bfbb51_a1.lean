-- Prove2me | solution 1 for WilliamsonShmoys.connected_simple_planar_edge_bound__p2m_0c722b40_f62a_4eb9_8c3e_41b6d8bfbb51_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:00:43.911316+00:00
-- url     : https://prove2.me/submissions/1f5a3c65-b6da-416c-99de-91c68928e9d8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_exists_mapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Theorems.Thm_WilliamsonShmoys_planarMapData_edge_bound__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a4
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : HasPlanarDrawingOn J)
    (hconn : forall u v : V, Nonempty (J.Walk u v))
    (hcard : 3 <= Fintype.card V) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    J.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  letI : DecidableRel J.Adj := Classical.decRel J.Adj
  have hmap :=
    WilliamsonShmoys.planarDrawingOn_exists_mapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
      J hJ hconn hcard
  cases hmap with
  | intro D =>
      exact WilliamsonShmoys.planarMapData_edge_bound__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a4 J D