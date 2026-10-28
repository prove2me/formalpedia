-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_extension_for_maximal_drawable_target
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:29:52.627281+00:00
-- url     : https://prove2.me/submissions/63182799-94de-4734-bd08-ec44ad2ba076
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationEulerData
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_on_vertex_type
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulated_sphere_face_data

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    exists L : SimpleGraph V,
      K <= L /\ WilliamsonShmoys.HasPlanarDrawingOn L /\
        Nonempty (WilliamsonShmoys.TriangulatedSphereFaceData L) := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_on_vertex_type K hK
  refine ⟨L, hKL, hL, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_has_triangulated_sphere_face_data
    L hL hCard hMax