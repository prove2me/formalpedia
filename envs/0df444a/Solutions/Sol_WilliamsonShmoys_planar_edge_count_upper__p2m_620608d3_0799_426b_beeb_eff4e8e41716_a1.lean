-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper__p2m_620608d3_0799_426b_beeb_eff4e8e41716_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:57:47.989864+00:00
-- url     : https://prove2.me/submissions/27e7da6c-2b0f-424a-9d2a-dd1574e8d46d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_of_connected__p2m_f1a10c6f_98ea_4f43_9f3f_2fa486717043_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_f1a10c6f_98ea_4f43_9f3f_2fa486717043_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hH, hconn, hmono⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_f1a10c6f_98ea_4f43_9f3f_2fa486717043_a1 K hK
  have hbound :=
    WilliamsonShmoys.planar_edge_count_upper_of_connected__p2m_f1a10c6f_98ea_4f43_9f3f_2fa486717043_a1 H hH hconn hcard
  omega