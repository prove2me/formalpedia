-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_data__p2m_abe9ada7_d03e_4dfe_be97_61dab793415e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:46:10.350719+00:00
-- url     : https://prove2.me/submissions/f6378255-78cf-49a9-8573-70480f4d1194

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_relation__p2m_dbab630e_c01d_4b47_9ab6_dd56c8211fc8_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_dbab630e_c01d_4b47_9ab6_dd56c8211fc8_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hConn : K.Connected)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    Exists (fun f : Nat => And
      (Fintype.card V + f = K.edgeSet.ncard + 2)
      (3 * f <= 2 * K.edgeSet.ncard)) := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_relation__p2m_dbab630e_c01d_4b47_9ab6_dd56c8211fc8_a1
      K hConn hK hCard
  have hedge :=
    WilliamsonShmoys.planar_drawing_edge_bound__p2m_dbab630e_c01d_4b47_9ab6_dd56c8211fc8_a1
      K hConn hK hCard
  exact Exists.intro f (And.intro heuler (by omega))