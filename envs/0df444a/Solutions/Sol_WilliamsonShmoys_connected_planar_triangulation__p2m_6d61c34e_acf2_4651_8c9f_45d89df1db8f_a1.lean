-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_triangulation__p2m_6d61c34e_acf2_4651_8c9f_45d89df1db8f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:51:46.977912+00:00
-- url     : https://prove2.me/submissions/7adc5b03-dcca-4317-a4b1-944815716a11

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_count__p2m_90a6eb8a_5322_4ab0_9f54_46d0ab83dbd2_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_90a6eb8a_5322_4ab0_9f54_46d0ab83dbd2_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ M : SimpleGraph V,
      K ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hKM, hM, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count__p2m_90a6eb8a_5322_4ab0_9f54_46d0ab83dbd2_a1
      K hplanar
  have hCount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_90a6eb8a_5322_4ab0_9f54_46d0ab83dbd2_a1
      M hM hV hMax
  exact ⟨M, hKM, hM, hCount.symm⟩