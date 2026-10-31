-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_upper_bound__p2m_b2b84f5d_edb7_4ceb_baef_13a00af24ad7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:30:49.784815+00:00
-- url     : https://prove2.me/submissions/4c4d700e-85ee-4001-b7e5-cc08da7281b0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_ddfe16f2_466b_4eda_98ed_20e5107df448_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ddfe16f2_466b_4eda_98ed_20e5107df448_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn R) (hV : 3 ≤ Fintype.card V) :
    R.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨T, hRT, hDrawT, hMax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_ddfe16f2_466b_4eda_98ed_20e5107df448_a1
      R hDraw
  have hCardLe : R.edgeSet.ncard ≤ T.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hRT)
  have hTri : 3 * Fintype.card V = T.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_ddfe16f2_466b_4eda_98ed_20e5107df448_a1
      T hDrawT hV hMax
  omega