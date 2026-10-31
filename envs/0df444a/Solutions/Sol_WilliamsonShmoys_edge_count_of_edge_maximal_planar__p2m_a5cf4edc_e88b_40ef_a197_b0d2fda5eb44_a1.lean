-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_edge_maximal_planar__p2m_a5cf4edc_e88b_40ef_a197_b0d2fda5eb44_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:18:27.444444+00:00
-- url     : https://prove2.me/submissions/0548adf3-a4e3-4b3e-a317-f97109f3e5fc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hDraw : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1 L hV hDraw
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1 L hV hDraw hMax
  omega