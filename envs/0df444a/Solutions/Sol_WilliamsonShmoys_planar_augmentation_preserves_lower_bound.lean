-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_preserves_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:13:42.273885+00:00
-- url     : https://prove2.me/submissions/6ffad780-deb9-40ba-9393-dcd5f6f1e57c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edgeMaximal_planar_supergraph
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_edgeMaximal_planar

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.exists_edgeMaximal_planar_supergraph K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.edge_bound_of_edgeMaximal_planar L hV hL hMax⟩