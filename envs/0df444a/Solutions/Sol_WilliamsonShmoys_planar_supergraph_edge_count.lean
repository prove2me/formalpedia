-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:37:15.678411+00:00
-- url     : https://prove2.me/submissions/8c5ee0cc-5557-4816-affc-d1e7cc25b728

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_extension_for_edge_bound
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_has_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_extension_for_edge_bound K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_drawable_extension_has_edge_bound L hL hV hmax⟩