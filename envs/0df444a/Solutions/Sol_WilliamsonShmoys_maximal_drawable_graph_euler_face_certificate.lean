-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_euler_face_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:23:40.307792+00:00
-- url     : https://prove2.me/submissions/55d9b117-fa93-47ca-be8c-674691457849
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_of_maximal_drawable
import Theorems.Thm_WilliamsonShmoys_planar_euler_face_count
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_planar_drawing

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ J : SimpleGraph V,
      K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ K) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * K.edgeSet.ncard := by
  have hconn :=
    WilliamsonShmoys.connected_of_maximal_drawable K hV hDraw hMax
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.planar_euler_face_count K hDraw hconn
  have hbound := WilliamsonShmoys.planar_edge_bound_of_planar_drawing K hV hDraw
  refine ⟨f, heuler, ?_⟩
  omega