-- Prove2me | solution 1 for WilliamsonShmoys_triangulation_supergraph_of_planar_drawing__p2m_02efd696_96fe_4670_9021_ba912a848fde_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:05:58.704032+00:00
-- url     : https://prove2.me/submissions/2f71123f-8dd4-4a7b-9f2f-0b3b0c97aadf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_a21b9daf_96c0_42bf_b053_e1966758807a_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_supergraph__p2m_a21b9daf_96c0_42bf_b053_e1966758807a_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        (letI : DecidableRel H.Adj := Classical.decRel H.Adj
         H.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  classical
  obtain ⟨H, hGH, hdrawH, hmax⟩ :=
    WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_a21b9daf_96c0_42bf_b053_e1966758807a_a1
      G hconn hdraw
  refine ⟨H, hGH, hdrawH, ?_⟩
  exact WilliamsonShmoys_edge_count_of_maximal_planar_supergraph__p2m_a21b9daf_96c0_42bf_b053_e1966758807a_a1
    H hcard (hconn.mono hGH) hdrawH hmax