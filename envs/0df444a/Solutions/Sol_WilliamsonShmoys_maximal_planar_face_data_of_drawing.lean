-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_data_of_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:53:52.956782+00:00
-- url     : https://prove2.me/submissions/c4973152-4b5f-44f8-bec0-2cc9c9a4324e

import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_for_triangulated_face_data
import Theorems.Thm_WilliamsonShmoys_face_data_of_edge_count_for_triangulated_planar_data

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K -> H <= K -> K <= H)
    (hV : 3 <= Fintype.card V) :
    Nonempty (WilliamsonShmoys.TriangulatedPlanarFaceData H) := by
  apply WilliamsonShmoys.face_data_of_edge_count_for_triangulated_planar_data H hV
  exact WilliamsonShmoys.maximal_planar_graph_edge_count_for_triangulated_face_data H hH hmax hV