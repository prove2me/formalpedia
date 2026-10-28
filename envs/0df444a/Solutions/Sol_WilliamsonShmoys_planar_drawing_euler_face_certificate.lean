-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:41:48.278153+00:00
-- url     : https://prove2.me/submissions/cd966459-f6f9-4a8d-8daf-7116408f3517
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_euler_certificate
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_euler_face_certificate

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (f : ℕ),
      H ≤ K ∧
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * K.edgeSet.ncard := by
  obtain ⟨K, hHK, hKDraw, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_for_euler_certificate H hV hDraw
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_drawable_graph_euler_face_certificate K hV hKDraw hMax
  exact ⟨K, f, hHK, hEuler, hFaces⟩