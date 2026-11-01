-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_upper_bound_of_connected__p2m_d428652f_4806_46f7_95cc_5b75c77bec4b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:29:15.75464+00:00
-- url     : https://prove2.me/submissions/d5716057-fd1d-4b49-bffd-c256b3ee34fd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_6c2189f4_b548_4ce1_a4dc_c9893d852748_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hFace⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count__p2m_6c2189f4_b548_4ce1_a4dc_c9893d852748_a1
      M dM hM hconn hcard
  omega