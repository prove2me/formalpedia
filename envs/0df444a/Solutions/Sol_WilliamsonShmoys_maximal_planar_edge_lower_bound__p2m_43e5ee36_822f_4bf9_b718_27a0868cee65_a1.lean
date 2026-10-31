-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_43e5ee36_822f_4bf9_b718_27a0868cee65_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:50:43.829113+00:00
-- url     : https://prove2.me/submissions/8f162bbb-75a1-4117-b1c3-4defead15d05

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_triangulation__p2m_02b7676f_a513_46e6_8e4a_f3d718372bb1_a3

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : forall J : SimpleGraph V, H <= J -> WilliamsonShmoys.HasPlanarDrawingOn J -> J = H)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= H.edgeSet.ncard := by
  obtain ⟨f, hEuler, hTriangulated⟩ :=
    WilliamsonShmoys.maximal_planar_face_triangulation__p2m_02b7676f_a513_46e6_8e4a_f3d718372bb1_a3
      H hDraw hMax hV
  omega