-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:50:46.867309+00:00
-- url     : https://prove2.me/submissions/e78cdfa6-8cb8-40d1-b6f2-291949cfe317

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_extends_to_triangulation__p2m_7d8f15aa_1389_4e26_88fc_ab77a83aea4e_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V - 6 = M.edgeSet.ncard := by
  obtain ⟨N, hMN, hN, hcount⟩ :=
    WilliamsonShmoys.planar_graph_extends_to_triangulation__p2m_7d8f15aa_1389_4e26_88fc_ab77a83aea4e_a2
      M hcard hM
  have hEq : N = M := hmax N hMN hN
  rw [hEq] at hcount
  exact hcount.symm