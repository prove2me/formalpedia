-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper__p2m_0b1d558b_5b99_484a_a69e_3ba1af67a959_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:49:59.69054+00:00
-- url     : https://prove2.me/submissions/ca6b0d30-f8a5-4b77-8062-b88e2497f2a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_f85cf95c_259e_403f_a3bb_5b4078926a26_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper__p2m_f85cf95c_259e_403f_a3bb_5b4078926a26_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hT : HasPlanarDrawingOn T) :
    T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hsub, hconn, hplanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_f85cf95c_259e_403f_a3bb_5b4078926a26_a1
      T hV hT
  calc
    T.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono hsub
    _ ≤ 3 * Fintype.card V - 6 :=
      WilliamsonShmoys.connected_planar_edge_upper__p2m_f85cf95c_259e_403f_a3bb_5b4078926a26_a1
        H hV hconn hplanar