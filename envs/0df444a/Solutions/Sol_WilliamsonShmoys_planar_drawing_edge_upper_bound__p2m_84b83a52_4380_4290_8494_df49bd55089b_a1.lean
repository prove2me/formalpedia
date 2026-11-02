-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_84b83a52_4380_4290_8494_df49bd55089b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T23:34:26.119445+00:00
-- url     : https://prove2.me/submissions/75f4077f-2d4d-4a5d-97d1-727afa8cec21

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_72c268f3_7cc5_487f_ad8b_d5f36984db50_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_72c268f3_7cc5_487f_ad8b_d5f36984db50_a1 N hN hcard