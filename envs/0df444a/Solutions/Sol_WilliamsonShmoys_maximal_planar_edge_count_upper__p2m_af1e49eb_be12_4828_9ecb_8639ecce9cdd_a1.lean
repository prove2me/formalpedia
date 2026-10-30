-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_af1e49eb_be12_4828_9ecb_8639ecce9cdd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:52:00.78966+00:00
-- url     : https://prove2.me/submissions/ed43e806-853a-4db5-9b9e-6b21e0e2f7c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_induce__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1
import Theorems.Thm_WilliamsonShmoys_edge_bound_from_connected_induced__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hLocal :
      ∀ (S : Finset V), 3 ≤ S.card →
        (L.induce (↑S : Set V)).Connected →
        (L.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * S.card := by
    intro S hS hConn
    have hDrawS :
        WilliamsonShmoys.HasPlanarDrawingOn (L.induce (↑S : Set V)) :=
      WilliamsonShmoys.planar_drawing_induce__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1
        L S hDraw
    have hCard : 3 ≤ Fintype.card {v // v ∈ S} := by
      simpa using hS
    have hBound :=
      WilliamsonShmoys.planar_connected_edge_bound__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1
        (L.induce (↑S : Set V)) hDrawS hConn hCard
    simpa using hBound
  exact WilliamsonShmoys.edge_bound_from_connected_induced__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1
    L hV hLocal