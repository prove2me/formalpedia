-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_2d721275_eabe_421b_ae9b_fc6b7bdcfafc_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:35:12.777525+00:00
-- url     : https://prove2.me/submissions/5f8e5719-f302-4b74-b9bb-c4465c73df8f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph__p2m_cc05e90a_af6b_4557_980d_9087018dc646_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨N, hMN, hN, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph__p2m_cc05e90a_af6b_4557_980d_9087018dc646_a1
      M hM hcard
  have hNM : N ≤ M := hMax N hMN hN
  have hEq : N = M := le_antisymm hNM hMN
  subst N
  exact hcount