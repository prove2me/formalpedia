-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_3be79666_71db_45ff_88b4_e34036e94e74_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:40:28.025516+00:00
-- url     : https://prove2.me/submissions/f2bdf30b-4254-4d20-8909-9d4468cf2d1d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_3bbe118b_2c52_4e44_a40f_aa9dcfe8d0b0_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_3bbe118b_2c52_4e44_a40f_aa9dcfe8d0b0_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ HasPlanarDrawingOn M ∧
        M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hMDraw, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_3bbe118b_2c52_4e44_a40f_aa9dcfe8d0b0_a1
      L hDraw
  refine ⟨M, hLM, hMDraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_3bbe118b_2c52_4e44_a40f_aa9dcfe8d0b0_a1
    M hMDraw hCard hMax