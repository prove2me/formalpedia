-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_dense_supergraph_f3620a14
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:00:53.678989+00:00
-- url     : https://prove2.me/submissions/a15e26cd-abe2-47b5-aad4-d7c6a23146fe

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_graph_has_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_maximal_drawable_graph_edge_bound

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      S ≤ R ∧
      3 * Fintype.card V - 6 ≤ R.edgeSet.ncard := by
  obtain ⟨R, hR, hSR, hmax⟩ :=
    WilliamsonShmoys.planar_drawable_graph_has_maximal_supergraph S hS
  exact ⟨R, hR, hSR,
    WilliamsonShmoys.planar_maximal_drawable_graph_edge_bound R hR hmax hCard⟩