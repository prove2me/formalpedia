-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_count__p2m_ccb6a6bc_2d03_4d79_9277_48639c2dde63_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:17:27.60398+00:00
-- url     : https://prove2.me/submissions/a623dcbe-f360-4539-b36f-7f233ede13fe

import Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_supergraph__p2m_1d9e4996_f1da_4af7_951a_5adb0b1eb381_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_of_maximal_drawable__p2m_1d9e4996_f1da_4af7_951a_5adb0b1eb381_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) (hCard : 3 ≤ Fintype.card V) : ∃ P : SimpleGraph V, Set.Subset N.edgeSet P.edgeSet ∧ HasPlanarDrawingOn P ∧ P.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨P, hNP, hP, hmax⟩ := WilliamsonShmoys.planar_drawable_maximal_supergraph__p2m_1d9e4996_f1da_4af7_951a_5adb0b1eb381_a1 N hN
  exact ⟨P, hNP, hP, WilliamsonShmoys.planar_edge_count_of_maximal_drawable__p2m_1d9e4996_f1da_4af7_951a_5adb0b1eb381_a1 P hP hCard hmax⟩