-- Prove2me | solution 1 for WilliamsonShmoys.has_triangular_map_of_maximal_planar_drawing__p2m_8b018285_4ad7_4c76_beb1_fed47f71a69b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:34:54.996212+00:00
-- url     : https://prove2.me/submissions/8ee794ac-5bc2-4db8-83e9-d9db81a0145f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extremality_implies_maximal__p2m_fe860f1c_6599_42e8_850c_50d6abf755f9_a12
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangular_map__p2m_fe860f1c_6599_42e8_850c_50d6abf755f9_a12

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    ∃ (F : Type) (instF : Fintype F),
      Nonempty (@WilliamsonShmoys.TriangularMap V ‹Fintype V› H F instF) := by
  have hMax :=
    WilliamsonShmoys.planar_drawing_extremality_implies_maximal__p2m_fe860f1c_6599_42e8_850c_50d6abf755f9_a12
      H hH hV hcount
  exact
    WilliamsonShmoys.maximal_planar_drawing_has_triangular_map__p2m_fe860f1c_6599_42e8_850c_50d6abf755f9_a12
      H hH hV hMax