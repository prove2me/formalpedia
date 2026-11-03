-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_3a4c1f5e_1776_4c15_8093_87a5faec746f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:27:01.443166+00:00
-- url     : https://prove2.me/submissions/abca23ff-4fe1-4bff-9b50-30a3eaac4f98

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count__p2m_45b42f5d_e929_44e5_b683_b600a07db038_a3
import Theorems.Thm_WilliamsonShmoys_planar_face_count_edge_bound__p2m_45b42f5d_e929_44e5_b683_b600a07db038_a3

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected) (hcard : 3 ≤ Fintype.card V) :
    M.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  have hfaces := WilliamsonShmoys.planar_drawing_face_count__p2m_45b42f5d_e929_44e5_b683_b600a07db038_a3
    M hM hconn hcard
  exact WilliamsonShmoys.planar_face_count_edge_bound__p2m_45b42f5d_e929_44e5_b683_b600a07db038_a3
    M hcard hfaces