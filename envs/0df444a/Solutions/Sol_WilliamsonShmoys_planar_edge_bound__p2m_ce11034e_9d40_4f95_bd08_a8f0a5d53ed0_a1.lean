-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound__p2m_ce11034e_9d40_4f95_bd08_a8f0a5d53ed0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:09:18.49304+00:00
-- url     : https://prove2.me/submissions/211ad427-5133-44e9-bdba-67c77b156ccd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_ce2523b8_2817_4847_92d2_52162bbbf3f4_a1
import Theorems.Thm_WilliamsonShmoys_planar_face_count_boundary_lower_bound__p2m_ce2523b8_2817_4847_92d2_52162bbbf3f4_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count__p2m_ce2523b8_2817_4847_92d2_52162bbbf3f4_a1
      M hM hconn
  have hFaces :=
    WilliamsonShmoys.planar_face_count_boundary_lower_bound__p2m_ce2523b8_2817_4847_92d2_52162bbbf3f4_a1
      M hM hconn hcard f hEuler
  omega