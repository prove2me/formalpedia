-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_card_lower_bound__p2m_26140456_b7e4_4d83_b9c1_39ddc27ba139_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:15:43.944193+00:00
-- url     : https://prove2.me/submissions/a6cb71fc-20c2-454d-b2a7-b3141db1b839
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_supergraph_edge_bound__p2m_57c283a7_68a4_4e3d_813f_6e392f4dfebc_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeFinset.card := by
  classical
  obtain ⟨N, hN, hMN, hNbound⟩ :=
    WilliamsonShmoys.planar_drawable_supergraph_edge_bound__p2m_57c283a7_68a4_4e3d_813f_6e392f4dfebc_a1
      M hM hcard
  have hNM : N ≤ M := hmax N hN hMN
  have hcardNM : N.edgeFinset.card ≤ M.edgeFinset.card := by
    exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hNM)
  exact hNbound.trans hcardNM