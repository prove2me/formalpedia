-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_edge_bound_maximal_case_7121c0f2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:39:56.351899+00:00
-- url     : https://prove2.me/submissions/9eb5fabb-7a82-4096-9e80-a34e0edef40f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_euler_face_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : forall H : SimpleGraph V, G <= H ->
      WilliamsonShmoys.HasPlanarDrawingOn H -> H <= G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_drawing_euler_face_count G hdraw hmax hV
  omega