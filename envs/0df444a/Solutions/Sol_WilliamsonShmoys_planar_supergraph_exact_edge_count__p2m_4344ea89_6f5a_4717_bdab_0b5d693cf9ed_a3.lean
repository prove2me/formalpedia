-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_exact_edge_count__p2m_4344ea89_6f5a_4717_bdab_0b5d693cf9ed_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:18:33.376916+00:00
-- url     : https://prove2.me/submissions/7414348a-fdf7-4249-8490-c4d9e8db5fc0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_ffd766b2_d86f_4f00_bea0_c76fad60558a_a2
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_count__p2m_ffd766b2_d86f_4f00_bea0_c76fad60558a_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hN, hMN, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_ffd766b2_d86f_4f00_bea0_c76fad60558a_a2
      M hM
  refine ⟨N, hN, hMN, ?_⟩
  exact WilliamsonShmoys.edge_maximal_planar_graph_edge_count__p2m_ffd766b2_d86f_4f00_bea0_c76fad60558a_a2
    N hN hcard hmax
