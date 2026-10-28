-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:09:00.907683+00:00
-- url     : https://prove2.me/submissions/30ce07ad-0abf-4a04-b0d1-84f7fa6b91c1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_admissible_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  exact WilliamsonShmoys.exists_maximal_admissible_supergraph G
    WilliamsonShmoys.HasPlanarDrawingOn hG