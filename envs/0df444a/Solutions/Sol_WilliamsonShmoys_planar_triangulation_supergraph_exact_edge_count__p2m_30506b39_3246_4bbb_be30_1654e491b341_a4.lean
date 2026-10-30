-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_30506b39_3246_4bbb_be30_1654e491b341_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:00:14.062+00:00
-- url     : https://prove2.me/submissions/8c26287d-2629-416f-9a07-d9ec6f1a2e5a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_completion__p2m_0fb3eb1a_7dcf_4fa9_a911_841bd56bc763_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_exact_count__p2m_0fb3eb1a_7dcf_4fa9_a911_841bd56bc763_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hN, hCount, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_edge_maximal_completion__p2m_0fb3eb1a_7dcf_4fa9_a911_841bd56bc763_a1
      M hM
  refine ⟨N, hMN, hN, hCount, ?_⟩
  exact WilliamsonShmoys.planar_edge_maximal_exact_count__p2m_0fb3eb1a_7dcf_4fa9_a911_841bd56bc763_a1
    M N hCard hMN hN hMax