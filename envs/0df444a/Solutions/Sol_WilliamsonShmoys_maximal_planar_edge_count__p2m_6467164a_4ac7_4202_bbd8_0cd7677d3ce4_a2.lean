-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_6467164a_4ac7_4202_bbd8_0cd7677d3ce4_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:31:52.925952+00:00
-- url     : https://prove2.me/submissions/260767e6-f2e2-41d5-af8c-6109e141c8de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_fb63e52b_62b1_491c_ab5d_ee94b001efe6_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_fb63e52b_62b1_491c_ab5d_ee94b001efe6_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card + 6 = 3 * Fintype.card V := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hupper := WilliamsonShmoys.planar_edge_upper_bound__p2m_fb63e52b_62b1_491c_ab5d_ee94b001efe6_a1 H hH hcard
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_fb63e52b_62b1_491c_ab5d_ee94b001efe6_a1 H hH hmax hcard
  omega