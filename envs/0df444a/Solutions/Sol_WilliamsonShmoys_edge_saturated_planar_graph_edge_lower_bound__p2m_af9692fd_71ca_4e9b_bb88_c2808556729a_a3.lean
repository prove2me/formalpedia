-- Prove2me | solution 1 for WilliamsonShmoys.edge_saturated_planar_graph_edge_lower_bound__p2m_af9692fd_71ca_4e9b_bb88_c2808556729a_a3
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:50:59.355793+00:00
-- url     : https://prove2.me/submissions/f857213b-4313-45a8-b336-42b6d883a033

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_subgraph

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hblocked : ∀ u v, u ≠ v → ¬ H.Adj u v →
      ∀ K : SimpleGraph V, H ≤ K → K.Adj u v →
        WilliamsonShmoys.HasPlanarDrawingOn K → False) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  have hMax' : ∀ J : SimpleGraph _, H ≤ J → HasPlanarDrawingOn J → J ≤ H := by
    intro J hHJ hJ
    intro u v hJuv
    by_contra hHuv
    let K : SimpleGraph V := H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}
    have hKJ : K ≤ J := sup_le hHJ (by
      intro x y hxy
      rw [SimpleGraph.fromEdgeSet_adj] at hxy
      obtain ⟨hxy, hne⟩ := hxy
      rw [Set.mem_singleton_iff, Sym2.eq_iff] at hxy
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hJuv
      · exact hJuv.symm)
    have hKuv : K.Adj u v := Or.inr (by simp [SimpleGraph.fromEdgeSet_adj, hJuv.ne])
    exact hblocked u v hJuv.ne hHuv K le_sup_left hKuv (WilliamsonShmoys.planar_drawingOn_subgraph hKJ hJ)
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc H hcard hH hMax'
  omega
