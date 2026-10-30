-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_f85cf95c_259e_403f_a3bb_5b4078926a26_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:05:26.252645+00:00
-- url     : https://prove2.me/submissions/f24fe3c0-5658-453e-9457-55ad0f80f8ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_property_connected_extension__p2m_c5002bd9_287e_4c4a_8f25_d9d45db0800d_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_growth_step__p2m_c5002bd9_287e_4c4a_8f25_d9d45db0800d_a2
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hT : HasPlanarDrawingOn T) :
    ∃ H : SimpleGraph V, T.edgeSet ⊆ H.edgeSet ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  classical
  obtain ⟨H, hsub, hdraw, hconn⟩ :=
    WilliamsonShmoys.finite_property_connected_extension__p2m_c5002bd9_287e_4c4a_8f25_d9d45db0800d_a2
      T HasPlanarDrawingOn hT
      (by
        intro G hG hdisc
        obtain ⟨H, hGH, hHdraw, hinc⟩ :=
          WilliamsonShmoys.planar_drawing_edge_growth_step__p2m_c5002bd9_287e_4c4a_8f25_d9d45db0800d_a2
            G hG hdisc
        exact ⟨H, hGH, hHdraw, hinc⟩)
  exact ⟨H, hsub, hconn, hdraw⟩