-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_1095f796_c580_4096_843f_cd051f083539_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:46:03.533291+00:00
-- url     : https://prove2.me/submissions/dfdd93cc-f9a7-49a1-8fc7-9a789335acb6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_7a1738f6_5642_467f_b376_eb6ed4a76310_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_from_connected_extension__p2m_7a1738f6_5642_467f_b376_eb6ed4a76310_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hKH, hHconn, hHplanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_7a1738f6_5642_467f_b376_eb6ed4a76310_a1
      K hK
  exact WilliamsonShmoys.planar_edge_count_from_connected_extension__p2m_7a1738f6_5642_467f_b376_eb6ed4a76310_a1
      K H hV hKH hHconn hHplanar