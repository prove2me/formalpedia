-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_637d5aff_c0b4_44ca_8441_714e49c98d9c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:28:21.096493+00:00
-- url     : https://prove2.me/submissions/082b495b-aaed-482f-8fd6-20f16cd10477

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_b60b6e39_2306_4060_9921_33eb7510d6ae_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound__p2m_b60b6e39_2306_4060_9921_33eb7510d6ae_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → L = M)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_b60b6e39_2306_4060_9921_33eb7510d6ae_a1
    L hDraw hCard
  have hLower := WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_b60b6e39_2306_4060_9921_33eb7510d6ae_a1
    L hDraw hMax hCard
  omega