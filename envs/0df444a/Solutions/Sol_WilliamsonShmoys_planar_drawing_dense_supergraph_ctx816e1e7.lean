-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_dense_supergraph_ctx816e1e7
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:01:33.483641+00:00
-- url     : https://prove2.me/submissions/39816928-b549-4423-a1b2-98c8628fbb3d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_dense_supergraph_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_edge_bound

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    exists S : SimpleGraph V,
      R <= S /\ WilliamsonShmoys.HasPlanarDrawingOn S /\
        3 * Fintype.card V <= S.edgeSet.ncard + 6 := by
  obtain ⟨S, hRS, hS, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_dense_supergraph_maximal_extension R hV hR
  exact ⟨S, hRS, hS,
    WilliamsonShmoys.planar_drawing_edge_maximal_edge_bound S hV hS hmax⟩