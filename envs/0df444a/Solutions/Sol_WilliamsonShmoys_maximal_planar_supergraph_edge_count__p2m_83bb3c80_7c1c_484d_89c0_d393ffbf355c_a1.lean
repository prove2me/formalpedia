-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:35:59.445201+00:00
-- url     : https://prove2.me/submissions/83f9847b-853d-4597-9080-020a8200946d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ (N : SimpleGraph V),
      (∀ u v, M.Adj u v → N.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      ∀ u v, N.Adj u v → M.Adj u v) :
    M.edgeFinset.card + 6 = 3 * Fintype.card V := by
  have hm : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by
    intro N hMN hN
    apply le_antisymm
    · exact hmax N (fun a b hab => hMN hab) hN
    · exact hMN
  have hc := WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1 M hcard hM hm
  have he : M.edgeSet.ncard = M.edgeFinset.card := by
    rw [← M.coe_edgeFinset]
    exact Set.ncard_coe_finset _
  rw [he] at hc
  omega
