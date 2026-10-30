-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:33:43.807908+00:00
-- url     : https://prove2.me/submissions/5bf57757-ac88-47ad-9edc-1a1fedc0e328

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_for_edge_bound_5164bdb5_exists_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_edge_count

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound_5164bdb5_exists_maximal_supergraph
      H hH
  refine ⟨K, hHK, hK, ?_⟩
  exact WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_edge_count
    K hV hK hmax
