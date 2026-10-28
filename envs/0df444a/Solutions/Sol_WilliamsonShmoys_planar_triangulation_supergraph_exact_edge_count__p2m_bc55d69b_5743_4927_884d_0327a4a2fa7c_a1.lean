-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_bc55d69b_5743_4927_884d_0327a4a2fa7c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:30:30.57951+00:00
-- url     : https://prove2.me/submissions/9080af86-6690-4a28-a476-4b6dd55a4f6d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_155e3131_f4ce_4fb5_b73d_ce5928aca9fe_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exact_edge_count__p2m_155e3131_f4ce_4fb5_b73d_ce5928aca9fe_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V - 6 = N.edgeSet.ncard := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_155e3131_f4ce_4fb5_b73d_ce5928aca9fe_a3
      M hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximal_planar_supergraph_exact_edge_count__p2m_155e3131_f4ce_4fb5_b73d_ce5928aca9fe_a3
      N hN hCard hmax⟩