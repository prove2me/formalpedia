-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_edge_bound__p2m_09878566_3989_4e48_bc10_98e236546b3d_a1__p2m_09878566_3989_4e48_bc10_98e236546b3d_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:38:16.936359+00:00
-- url     : https://prove2.me/submissions/f15a7787-55a6-44e2-8ba3-972f85ef2009
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_euler_face_counts__p2m_22003a04_aff0_4d5b_b1d3_902c88d5c97f_a2
import Theorems.Thm_WilliamsonShmoys_euler_face_counts_edge_bound__p2m_22003a04_aff0_4d5b_b1d3_902c88d5c97f_a3
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨edgeCount, faceCount, hEdges, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planar_drawing_has_euler_face_counts__p2m_22003a04_aff0_4d5b_b1d3_902c88d5c97f_a2
      G hcard hconn hG
  exact WilliamsonShmoys.euler_face_counts_edge_bound__p2m_22003a04_aff0_4d5b_b1d3_902c88d5c97f_a3
    G edgeCount faceCount hEdges hEuler hFaces
