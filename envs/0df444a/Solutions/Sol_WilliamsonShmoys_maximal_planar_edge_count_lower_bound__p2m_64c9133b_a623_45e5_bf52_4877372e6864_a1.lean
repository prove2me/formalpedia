-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_64c9133b_a623_45e5_bf52_4877372e6864_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:44:05.806202+00:00
-- url     : https://prove2.me/submissions/7271c3f4-57ee-4096-ae3f-12ec95df8b7a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_count_certificate__p2m_8c314bc4_0fdc_4634_a839_40069b48478f_a2
import Theorems.Thm_WilliamsonShmoys_planar_face_count_certificate_edge_bound__p2m_8c314bc4_0fdc_4634_a839_40069b48478f_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall Q : SimpleGraph V,
      (forall {u v : V}, P.Adj u v -> Q.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn Q ->
      (forall {u v : V}, Q.Adj u v -> P.Adj u v)) :
    letI : DecidableRel P.Adj := Classical.decRel P.Adj
    3 * Fintype.card V - 6 <= P.edgeFinset.card := by
  have hcert :=
    WilliamsonShmoys.maximal_planar_drawing_face_count_certificate__p2m_8c314bc4_0fdc_4634_a839_40069b48478f_a2
      P hP hcard hmax
  cases hcert with
  | intro F hF =>
    exact WilliamsonShmoys.planar_face_count_certificate_edge_bound__p2m_8c314bc4_0fdc_4634_a839_40069b48478f_a2
      P F hF.1 hF.2 hcard