-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_94c3c327_8601_4c2d_adbc_08897459bc6e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:25:36.74118+00:00
-- url     : https://prove2.me/submissions/2cde053d-e6e6-4105-a722-311bea186c79
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension__p2m_aba97578_a55f_467d_b26f_e953a5f6767e_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_card_eq__p2m_aba97578_a55f_467d_b26f_e953a5f6767e_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHplanar, hEdges, hMax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_aba97578_a55f_467d_b26f_e953a5f6767e_a1
      G hV hG
  have hEq := WilliamsonShmoys.edge_maximal_planar_graph_card_eq__p2m_aba97578_a55f_467d_b26f_e953a5f6767e_a1
    H hV hHplanar hMax
  omega