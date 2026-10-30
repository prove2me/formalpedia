-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_euler_and_face_degree_bound__p2m_41c4318d_ce97_4723_a74a_87f78274716c_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:03:07.235232+00:00
-- url     : https://prove2.me/submissions/767cc876-8453-463e-88f9-8a6538ebbc09

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_face_count__p2m_74636254_a954_4b01_9b70_979bcb3da8e1_a3
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_74636254_a954_4b01_9b70_979bcb3da8e1_a3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) :
    exists f : Nat,
      Fintype.card V + f = G.edgeSet.ncard + 2 /\
      3 * f <= 2 * G.edgeSet.ncard := by
  obtain ⟨f, heuler⟩ := WilliamsonShmoys.connected_drawing_euler_face_count__p2m_74636254_a954_4b01_9b70_979bcb3da8e1_a3 G hdraw hconn
  have hedge := WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_74636254_a954_4b01_9b70_979bcb3da8e1_a3 G hdraw hV
  refine ⟨f, heuler, ?_⟩
  omega