-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph_for_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:32:51.124751+00:00
-- url     : https://prove2.me/submissions/95d54880-1c0b-423d-af4d-fa07305e24d1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_finite_property

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet → K.edgeSet ≠ L.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn L := by
  exact WilliamsonShmoys.exists_maximal_supergraph_for_finite_property
    WilliamsonShmoys.HasPlanarDrawingOn H hHdraw