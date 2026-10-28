-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulation_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:16:35.219995+00:00
-- url     : https://prove2.me/submissions/1c11fd89-a100-4ff4-9323-c4e7bd8e5ae7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_85252b40_ee02_4664_960a_c8af730317d2
import Theorems.Thm_WilliamsonShmoys_triangular_plane_face_system_edge_count_85252b40_ee02_4664_960a_c8af730317d2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] [DecidableEq V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V ∧
      WilliamsonShmoys.HasTriangularPlaneFaceSystem K := by
  obtain ⟨K, hHK, hKdraw, hKfaces⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_85252b40_ee02_4664_960a_c8af730317d2
      H hV hH
  have hKedges :=
    WilliamsonShmoys.triangular_plane_face_system_edge_count_85252b40_ee02_4664_960a_c8af730317d2
      K hKfaces
  exact ⟨K, hHK, hKdraw, hKedges, hKfaces⟩