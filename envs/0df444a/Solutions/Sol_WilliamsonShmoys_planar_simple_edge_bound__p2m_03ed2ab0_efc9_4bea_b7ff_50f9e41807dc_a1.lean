-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound__p2m_03ed2ab0_efc9_4bea_b7ff_50f9e41807dc_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:50:51.86485+00:00
-- url     : https://prove2.me/submissions/9cfe4064-8a55-4229-a3b3-abbe63babe08
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_a4df0fa7_688f_4bd0_bfe4_ea6603f7e8eb_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_a4df0fa7_688f_4bd0_bfe4_ea6603f7e8eb_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨P, hKP, hP, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_a4df0fa7_688f_4bd0_bfe4_ea6603f7e8eb_a1
      K hK
  have hsub : K.edgeSet ⊆ P.edgeSet := hKP
  have hmono : K.edgeSet.ncard ≤ P.edgeSet.ncard := Set.ncard_mono hsub
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_bound__p2m_a4df0fa7_688f_4bd0_bfe4_ea6603f7e8eb_a1
      P hP hCard hmax
  omega