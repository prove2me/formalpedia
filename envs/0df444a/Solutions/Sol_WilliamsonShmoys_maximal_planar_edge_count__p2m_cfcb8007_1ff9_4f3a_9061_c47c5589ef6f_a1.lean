-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_cfcb8007_1ff9_4f3a_9061_c47c5589ef6f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:53:14.311202+00:00
-- url     : https://prove2.me/submissions/a75ba01b-ac5c-41c8-80a0-b9c89e27bee6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_exact_edge_count__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, HasPlanarDrawingOn N →
      (∀ u v, M.Adj u v → N.Adj u v) →
      ∀ u v, N.Adj u v → M.Adj u v) :
    letI : DecidableRel M.Adj := Classical.decRel M.Adj
    3 * Fintype.card V = M.edgeFinset.card + 6 := by
  classical
  have hm : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by
    intro N hMN hN
    ext u v
    exact ⟨hmax N hN (fun _ _ h => hMN h) u v, fun h => hMN h⟩
  have hc := WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1 M hM hV hm
  have he : M.edgeSet.ncard = M.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [he] at hc
  exact hc.symm
