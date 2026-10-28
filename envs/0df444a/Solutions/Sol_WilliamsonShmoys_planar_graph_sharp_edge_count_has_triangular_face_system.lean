-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_sharp_edge_count_has_triangular_face_system
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:42:06.665472+00:00
-- url     : https://prove2.me/submissions/49e17073-4904-43d0-9875-76846768ce82
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem
import Theorems.Thm_WilliamsonShmoys_sharp_planar_drawing_has_triangle_face_system
import Theorems.Thm_WilliamsonShmoys_triangle_face_system_incidence_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hedge : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    WilliamsonShmoys.HasTriangularPlaneFaceSystem H := by
  obtain ⟨faces, hcard, hadj, hincidence⟩ :=
    WilliamsonShmoys.sharp_planar_drawing_has_triangle_face_system
      H hV hH hedge
  have hcount :=
    WilliamsonShmoys.triangle_face_system_incidence_count
      H faces hcard hadj hincidence
  refine ⟨faces, hcard, hadj, hincidence, ?_⟩
  omega