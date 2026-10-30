-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper__p2m_1563787d_1e9d_4e0d_aca3_7df10f22af54_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:45:06.371308+00:00
-- url     : https://prove2.me/submissions/744d1614-1628-4ed5-adc5-1506daaa3c05
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  classical
  obtain ⟨K, hHK, hKdraw, hKconn, hKmax, hHKcard⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a2
      H hH hconn
  have hKbound :=
    WilliamsonShmoys.maximal_planar_edge_bound__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a2
      K hKdraw hKconn hV hKmax
  omega