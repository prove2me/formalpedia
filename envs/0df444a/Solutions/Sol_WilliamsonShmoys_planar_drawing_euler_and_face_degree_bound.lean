-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_and_face_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:38:47.403713+00:00
-- url     : https://prove2.me/submissions/dab52c04-033a-4652-9fe2-8d2d970d5bfe

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_job_d022b1d1_d1e3_4932_940e_a619c500f998
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_job_d022b1d1_d1e3_4932_940e_a619c500f998

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ f : Nat, Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f <= 2 * G.edgeSet.ncard := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count_job_d022b1d1_d1e3_4932_940e_a619c500f998
      G hdraw hconn
  have hedge :=
    WilliamsonShmoys.planar_simple_graph_edge_bound_job_d022b1d1_d1e3_4932_940e_a619c500f998
      G hdraw hconn hV
  refine ⟨f, heuler, ?_⟩
  omega