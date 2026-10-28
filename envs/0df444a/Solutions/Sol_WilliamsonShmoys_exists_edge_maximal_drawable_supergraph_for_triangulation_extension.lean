-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_drawable_supergraph_for_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:14:45.658617+00:00
-- url     : https://prove2.me/submissions/8ba77795-79df-4d4c-a95c-e92ca7dc89db

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_finite_graph_property

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hYdraw : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V, Y ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      ∀ W : SimpleGraph V, Z ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ Z := by
  exact WilliamsonShmoys.exists_maximal_supergraph_for_finite_graph_property
    WilliamsonShmoys.HasPlanarDrawingOn Y hYdraw
