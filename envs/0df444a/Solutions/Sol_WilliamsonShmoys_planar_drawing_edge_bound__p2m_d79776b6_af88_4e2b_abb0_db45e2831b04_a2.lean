-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_d79776b6_af88_4e2b_abb0_db45e2831b04_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:16:54.832981+00:00
-- url     : https://prove2.me/submissions/6d20a38f-de20-4a9c-81e4-51a4c4487478

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_mono__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  classical
  obtain ⟨M, hKM, hM, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3 K hK hV
  have hCount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3 M hM hV hMax
  have hMono :=
    WilliamsonShmoys.planar_drawing_edge_count_mono__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3 K M hKM
  omega