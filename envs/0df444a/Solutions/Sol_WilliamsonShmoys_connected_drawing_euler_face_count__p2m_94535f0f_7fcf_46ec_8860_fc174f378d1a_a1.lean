-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_euler_face_count__p2m_94535f0f_7fcf_46ec_8860_fc174f378d1a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:15:32.582717+00:00
-- url     : https://prove2.me/submissions/23f672ff-4665-44d4-9fc0-cda4a4a72572

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_faces__p2m_09878566_3989_4e48_bc10_98e236546b3d_a1__p2m_09878566_3989_4e48_bc10_98e236546b3d_a2
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_09878566_3989_4e48_bc10_98e236546b3d_a1__p2m_09878566_3989_4e48_bc10_98e236546b3d_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ,
      f + Fintype.card V = G.edgeSet.ncard + 2 ∧
      3 * f <= 2 * G.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.connected_planar_drawing_euler_faces__p2m_09878566_3989_4e48_bc10_98e236546b3d_a1__p2m_09878566_3989_4e48_bc10_98e236546b3d_a2
      G hconn hG
  have hEdge :=
    WilliamsonShmoys.simple_planar_edge_bound__p2m_09878566_3989_4e48_bc10_98e236546b3d_a1__p2m_09878566_3989_4e48_bc10_98e236546b3d_a2
      G hcard hconn hG
  refine ⟨f, hEuler, ?_⟩
  omega