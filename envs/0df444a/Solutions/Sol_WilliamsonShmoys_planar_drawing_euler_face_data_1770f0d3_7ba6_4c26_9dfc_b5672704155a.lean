-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_data_1770f0d3_7ba6_4c26_9dfc_b5672704155a
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:39:37.55667+00:00
-- url     : https://prove2.me/submissions/c97a8d4b-8216-47e3-8232-136d8d426ea5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_characteristic__p2m_47870a7b_cca6_4de2_8960_61ca392c7e1a_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_boundary_bound__p2m_47870a7b_cca6_4de2_8960_61ca392c7e1a_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hconn : K.Connected) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    Exists fun (F : Nat) =>
      And (Fintype.card V + F = K.edgeSet.ncard + 2)
        (3 * F <= 2 * K.edgeSet.ncard) := by
  have hEulerEx :=
    WilliamsonShmoys.planar_drawing_euler_characteristic__p2m_47870a7b_cca6_4de2_8960_61ca392c7e1a_a1
      K hconn hdraw
  exact hEulerEx.elim (fun F hEuler =>
    Exists.intro F (And.intro hEuler
      (WilliamsonShmoys.planar_drawing_face_boundary_bound__p2m_47870a7b_cca6_4de2_8960_61ca392c7e1a_a1
        K hconn hdraw hV F hEuler)))