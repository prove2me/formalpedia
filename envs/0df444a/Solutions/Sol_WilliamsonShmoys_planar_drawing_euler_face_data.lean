-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:31:44.159992+00:00
-- url     : https://prove2.me/submissions/8a55cc0f-a4fe-47a1-bcfe-e46f992c0a6e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_count_from_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_incidence_bound_from_drawing

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f <= 2 * G.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_count_from_drawing G hdraw hconn
  refine ⟨f, hEuler, ?_⟩
  exact WilliamsonShmoys.planar_drawing_incidence_bound_from_drawing
    G hdraw hconn hV f hEuler