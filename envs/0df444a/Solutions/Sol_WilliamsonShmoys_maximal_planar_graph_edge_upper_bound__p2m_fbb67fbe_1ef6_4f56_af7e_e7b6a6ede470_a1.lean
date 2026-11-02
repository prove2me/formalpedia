-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_upper_bound__p2m_fbb67fbe_1ef6_4f56_af7e_e7b6a6ede470_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:21:44.694227+00:00
-- url     : https://prove2.me/submissions/140843b0-5056-4e3b-8343-1ad5f2969d6d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_upper_bound_of_connected__p2m_d428652f_4806_46f7_95cc_5b75c77bec4b_a1
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_upper_bound_of_components__p2m_d428652f_4806_46f7_95cc_5b75c77bec4b_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  exact WilliamsonShmoys.planar_graph_edge_upper_bound_of_components__p2m_d428652f_4806_46f7_95cc_5b75c77bec4b_a1
    (by
      intro U _ _ N dN hN hconn hU
      exact WilliamsonShmoys.planar_graph_edge_upper_bound_of_connected__p2m_d428652f_4806_46f7_95cc_5b75c77bec4b_a1
        N dN hN hconn hU)
    M dM hM hcard