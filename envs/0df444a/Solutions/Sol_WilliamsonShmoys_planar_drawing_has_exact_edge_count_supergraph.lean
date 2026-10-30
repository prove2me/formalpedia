-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:57:58.961058+00:00
-- url     : https://prove2.me/submissions/3d3c3cdb-49c1-4ae7-8403-3e49166cf0b1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_drawable_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_exact_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hNK, hK, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_drawable_supergraph N hN
  exact ⟨K, hNK, hK,
    WilliamsonShmoys.maximal_drawable_graph_exact_edge_count K hK hMax hCard⟩