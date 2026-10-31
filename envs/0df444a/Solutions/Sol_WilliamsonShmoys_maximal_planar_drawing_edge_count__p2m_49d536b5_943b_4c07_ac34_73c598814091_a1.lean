-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_49d536b5_943b_4c07_ac34_73c598814091_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:30:20.252433+00:00
-- url     : https://prove2.me/submissions/e3b12d05-89ff-4f7c-a8b4-8052d6e90af5

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) : M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4 M hM hCard hMax
