-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_exists_mapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:38:47.057965+00:00
-- url     : https://prove2.me/submissions/86fffbd6-5f80-45f8-b8ec-d9986150d285
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edge_bound__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6
import Theorems.Thm_WilliamsonShmoys_connected_edge_lower_bound__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6
import Theorems.Thm_WilliamsonShmoys_planarMapData_of_edge_bounds__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (hJ : HasPlanarDrawingOn J)
    (hconn : forall u v : V, Nonempty (J.Walk u v))
    (hcard : 3 <= Fintype.card V) :
    Nonempty (PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3 J) := by
  have hlow := WilliamsonShmoys.connected_edge_lower_bound__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6 J hconn
  have hupp := WilliamsonShmoys.planarDrawingOn_edge_bound__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6 J hJ hcard
  exact WilliamsonShmoys.planarMapData_of_edge_bounds__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6 J hcard hlow hupp