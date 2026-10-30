-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal__p2m_fddb0f81_7944_4e99_898d_d807c45592e3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T18:43:27.280466+00:00
-- url     : https://prove2.me/submissions/3292ade8-7af2-45d3-9938-d6148146494a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_graph_supergraph_maximal__p2m_28855b7d_97e7_45b7_8e9d_f25fb9faa535_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        Set.Subset L.edgeSet M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet = L.edgeSet := by
  exact finite_graph_supergraph_maximal__p2m_28855b7d_97e7_45b7_8e9d_f25fb9faa535_a1
    K WilliamsonShmoys.HasPlanarDrawingOn hK